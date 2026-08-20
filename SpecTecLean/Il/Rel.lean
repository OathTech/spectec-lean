import SpecTecLean.Il.Eval
/-!
Relation execution: bounded, deterministic derivability search for `RelD`
rules (arc-2 stage 6). This layer has NO OCaml IL-level counterpart —
upstream compiles relations to AL algorithms (il2al); the charter's
faithful-but-slow decision is to execute the RULES DIRECTLY:

- A relation invocation supplies the first `k` conclusion components as
  ground INPUTS; the remaining components are OUTPUTS.
- Rules are tried in spec order (mirroring the deterministic choice the
  AL compilation makes); the first rule whose input patterns match and
  whose premises hold produces the outputs (reduced under the match
  substitution).
- Pattern matching REUSES `Eval.matchExp'` (concrete-vs-pattern, exactly
  its design). An `Irred`/no-match tries the next candidate.
- Premises reuse `Eval.reducePrem` semantics except `RulePr`, which
  recurses into this engine (Eval.reducePrem returns `unknown` for it,
  eval.ml:543).
- **Sequence splitting**: context rules like `Step/ctxt-instrs`
  (4.3-execution.instructions.spectec:32-35) match `val* instr* instr_1*`
  — a CatE chain of variable iterations with no literal anchors, which
  `matchExp'` cannot decide (Irred). For a concrete `ListE`, we enumerate
  boundary positions left-to-right (shortest earlier components first)
  and take the first split for which the rest of the rule succeeds.
  Bounded and deterministic; wasm's determinism makes the first success
  canonical.

Everything is fueled like Il/Eval.lean; `.fuel` is never caught.
-/

namespace SpecTecLean.Il

namespace Rel

open Eval

/-- Flatten a `CatE` chain into components (left-assoc as elaborated). -/
def catChain : Exp → List Exp
  | .mk (.catE e1 e2) _ => catChain e1 ++ catChain e2
  | e => [e]

/-- Is this component a variable-iteration (e.g. `val*`) that can absorb
an arbitrary sublist? -/
def isVarIter : Exp → Bool
  | .mk (.iterE _ (.mk _ _)) _ => true
  | _ => false

mutual

/-- Try to match a list of pattern components against a concrete element
list, enumerating boundaries for variable-iteration components
(shortest-first). Returns the extended substitution. -/
def matchSeq (env : Env) (fuel : Nat) (s : Subst) (pats : List Exp)
    (elems : List Exp) (elemTyp : Typ) (k : Nat) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match pats with
    | [] => if elems.isEmpty then pure (some s) else pure none
    | [p] =>
      -- last component absorbs the rest
      matchComponent env n s p elems elemTyp
    | p :: ps =>
      if isVarIter p then
        -- enumerate the split point, shortest prefix first
        (List.range (elems.length + 1)).findSomeM? (fun len => do
          let pre := elems.take len
          let post := elems.drop len
          catchIrred
            (do
              match ← matchComponent env n s p pre elemTyp with
              | none => pure none
              | some s' => matchSeq env n s' ps post elemTyp k)
            (fun _ => pure none))
      else do
        -- fixed-arity component: consumes exactly one element
        match elems with
        | [] => pure none
        | e0 :: rest => do
          let r ← catchIrred
            (do matchExp' env n s e0 p)
            (fun _ => pure none)
          match r with
          | none => pure none
          | some s' => matchSeq env n s' ps rest elemTyp k

/-- Match one pattern component against a concrete SUBLIST (as a ListE). -/
def matchComponent (env : Env) (fuel : Nat) (s : Subst) (p : Exp)
    (elems : List Exp) (elemTyp : Typ) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    let concrete : Exp := .mk (.listE elems) (.iterT elemTyp .list)
    catchIrred (matchExp' env n s concrete p) (fun _ => pure none)

end

/-- Input arity convention per relation: components before the arrow are
inputs. Fixed here for the wasm execution relations; extended as the
harness grows. Fails closed for unknown multi-component relations. -/
def inputArity (x : Id) (comps : List Exp) : EvalM Nat :=
  if x == "Step" || x == "Step_pure" || x == "Step_read" || x == "Steps"
  then pure 1
  else if x == "Eval_expr" then pure 2
  else if comps.length == 1 then pure 1  -- pure judgment: check only
  else Eval.err s!"relation {x}: no input-arity convention registered (extend Rel.inputArity)"

/-- The relation registry passes the derivation function down so premises
can recurse; `k` inputs convention per relation (see header). -/
structure RelCall where
  rel : Id
  inputs : List Exp

/-- Result of a derivation. -/
inductive DeriveRes where
  | ok (outputs : List Exp)
  | noRule          -- no rule applies (normal termination for Step)
  | stuck (msg : String)
deriving Inhabited

/-- Split a conclusion expression into its mixop components.
Relation conclusions are tuples of the mixop's arity (or a single
component for arity 1). -/
def components (e : Exp) : List Exp :=
  match e.it with
  | .tupE es => es
  | _ => [e]

mutual

/-- Check premises under `s`, in order; RulePr recurses into `derive`.
Mirrors the reducePrems threading (union of accumulated substs). -/
def checkPrems (env : Env) (fuel : Nat) (s : Subst) :
    List Prem → EvalM (Option Subst) :=
  fun prems =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prems with
    | [] => pure (some s)
    | prem :: rest => do
      let prem' ← liftS (Subst.substPremsOpt s [prem])
      let prem' := prem'.headD prem
      match prem' with
      | .rulePr x _args _op e => do
        -- premise components: bound prefix = inputs, unbound suffix = outs
        let comps := components e
        let (ps, mixop, _t, rules) ← match env.findRel? x with
          | some d => pure d
          | none => err s!"undeclared relation {x}"
        let _ := ps
        let k ← inputArity x comps
        let ins ← (comps.take k).mapM (fun c => reduceExp env n c)
        match ← derive env n x mixop rules ins k with
        | .ok outs =>
          -- bind output patterns against derived outputs
          let r ← (outs.zip (comps.drop k)).foldlM
            (fun (acc : Option Subst) cp => do
              match acc with
              | none => pure none
              | some sA =>
                catchIrred (matchExp' env n sA cp.1 cp.2)
                  (fun _ => pure none))
            (some s)
          match r with
          | none => pure none
          | some s' => checkPrems env n s' rest
        | _ => pure none
      | .ifPr e => do
        match (← reduceExp env n e).it with
        | .boolE true => checkPrems env n s rest
        | .boolE false => pure none
        | _ => pure none  -- undecidable premise: rule does not apply
      | .elsePr => checkPrems env n s rest
      | .letPr _ e1 e2 => do
        let r ← catchIrred
          (do
            match ← matchExp env n Subst.empty e2 e1 with
            | some s' => pure (some s')
            | none => pure none)
          (fun _ => pure none)
        match r with
        | none => pure none
        | some s' => checkPrems env n (Subst.union s s') rest
      | .iterPr _ _ | .negPr _ => do
        -- reuse Eval's premise reduction (handles Iter/Neg over the
        -- non-RulePr premise classes)
        match ← reducePrem env n prem' with
        | .yes s' => checkPrems env n (Subst.union s s') rest
        | .no => pure none
        | .unknown => pure none



/-- Derive one step of relation `x` with `k` ground inputs. Rules tried
in spec order; sequence-split fallback for CatE-chain conclusions. -/
def derive (env : Env) (fuel : Nat) (x : Id) (_mixop : Mixop)
    (rules : List Rule) (ins : List Exp) (k : Nat) : EvalM DeriveRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match rules with
    | [] => pure .noRule
    | .mk _rname _ _qs _op concl prems :: rest => do
      let comps := components concl
      if comps.length < k then
        err s!"relation {x}: conclusion arity below input count"
      else do
        let pats := comps.take k
        -- match each input component (sequence-split fallback for
        -- CatE-chain patterns over concrete lists: context rules)
        let mi ← (ins.zip pats).foldlM
          (fun (acc : Option Subst) cp => do
            match acc with
            | none => pure none
            | some sA =>
              catchIrred (matchExp' env n sA cp.1 cp.2)
                (fun _ => do
                  match cp.1.it, cp.2.it with
                  | .listE elems, .catE _ _ => do
                    let elemTyp := match cp.1.note with
                      | .iterT t _ => t
                      | t => t
                    matchSeq env n sA (catChain cp.2) elems elemTyp k
                  | _, _ => pure none))
          (some Subst.empty)
        match mi with
        | none => derive env n x _mixop rest ins k
        | some s => do
          match ← checkPrems env n s prems with
          | none => derive env n x _mixop rest ins k
          | some s' => do
            let outs ← (comps.drop k).mapM (fun c => do
              reduceExp env n (← liftS (Subst.substExpOpt s' c)))
            pure (.ok outs)

end

end Rel

end SpecTecLean.Il
