import SpecTecLean.Il.Eval
import SpecTecLean.Il.ToSexpr
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

/-- Statically-known element count of a FIXED (non-iteration) chain
component: a `listE` group, possibly behind `subE` wrappers. In
elaborated IL every literal instruction group in a `cat` chain is a
listE (audit 2026-08-21 dim2-1/V1: matching them element-wise made
mid-chain groups — Step_pure/trap-instrs, Step_read/throw_ref-instrs —
unmatchable). `none` = length not statically determinable; the use site
FAILS CLOSED on it, never mis-consuming. -/
def groupLen : Exp → Option Nat
  | .mk (.listE es) _ => some es.length
  | .mk (.subE e _ _) _ => groupLen e
  | _ => none

mutual

/-- CPS sequence matcher: match pattern components against a concrete
element list, enumerating boundaries for variable-iteration components
(shortest-first), and accept the FIRST enumeration for which the
continuation `k` (the rest of the rule: remaining inputs + premises)
succeeds. Premise-aware backtracking: a split that matches locally but
fails the continuation is not committed. -/
def matchSeqK (env : Env) (fuel : Nat) (s : Subst) (pats : List Exp)
    (elems : List Exp) (elemTyp : Typ)
    (k : Subst → EvalM (Option Subst)) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match pats with
    | [] => if elems.isEmpty then k s else pure none
    | [p] => do
      -- last component absorbs the rest
      match ← matchComponent env n s p elems elemTyp with
      | none => pure none
      | some s' => k s'
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
              | some s' => matchSeqK env n s' ps post elemTyp k)
            (fun _ => pure none))
      else do
        -- fixed GROUP component: consume exactly its statically-known
        -- element count and match as a list (see groupLen; fail closed
        -- when the count is undeterminable)
        match groupLen p with
        | none => pure none
        | some m =>
          if elems.length < m then pure none else do
          let r ← catchIrred
            (do matchComponent env n s p (elems.take m) elemTyp)
            (fun _ => pure none)
          match r with
          | none => pure none
          | some s' => matchSeqK env n s' ps (elems.drop m) elemTyp k

/-- Match one pattern component against a concrete SUBLIST (as a ListE). -/
def matchComponent (env : Env) (fuel : Nat) (s : Subst) (p : Exp)
    (elems : List Exp) (elemTyp : Typ) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    let concrete : Exp := .mk (.listE elems) (.iterT elemTyp .list)
    catchIrred (matchExp' env n s concrete p) (fun _ => pure none)

/-- CPS input-component matcher: plain `matchExp'` first; on
Irred/no-match, decompose case/tup wrappers pairwise and sequence-split
where a concrete list meets a `CatE`-chain pattern (context rules nest
the chain INSIDE the config case — Step/ctxt-instrs). Engine-level rule
for DERIVATION INPUTS only (logged); enumeration alternatives exist only
on the decomposition path — a direct matchExp' success is committed. -/
def matchInputK (env : Env) (fuel : Nat) (s : Subst) (concrete pat : Exp)
    (k : Subst → EvalM (Option Subst)) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let r ← catchIrred (matchExp' env n s concrete pat) (fun _ => pure none)
    match r with
    | some s' => k s'
    | none => matchInputDecompK env n s concrete pat k

def matchInputDecompK (env : Env) (fuel : Nat) (s : Subst)
    (concrete pat : Exp) (k : Subst → EvalM (Option Subst)) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match concrete.it, pat.it with
    | .caseE op1 p1, .caseE op2 p2 =>
      if eqMixop op1 op2 then matchInputK env n s p1 p2 k else pure none
    | .tupE es1, .tupE es2 =>
      if es1.length == es2.length then
        matchInputsK env n s (es1.zip es2) k
      else pure none
    | .listE elems, .catE _ _ =>
      let elemTyp := match concrete.note with
        | .iterT t _ => t
        | t => t
      matchSeqK env n s (catChain pat) elems elemTyp k
    | _, _ => pure none

/-- Fold `matchInputK` over (concrete, pattern) pairs, CPS. -/
def matchInputsK (env : Env) (fuel : Nat) (s : Subst)
    (prs : List (Exp × Exp)) (k : Subst → EvalM (Option Subst)) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prs with
    | [] => k s
    | cp :: rest =>
      matchInputK env n s cp.1 cp.2 (fun s' =>
        matchInputsK env n s' rest k)

end

/-- Input arity convention per relation: components before the arrow are
inputs. Fixed here for the wasm execution relations; extended as the
harness grows. Fails closed for unknown multi-component relations.

WARNING (audit dim2-2/V8): before registering a MULTI-OUTPUT
relation that has a self-subsumption rule (same inputs, different
output — Ref_ok, Externaddr_ok, Instrs_ok, Instrs_ok2 all have `/sub`
rules), the visited-guard limitation documented at `derive` must be
solved; the guard would refuse the subsumption premise and silently
under-derive (e.g. every ref.test/ref.cast/br_on_cast needing
subsumption would fall to its otherwise-sibling). The fail-closed
error below is what currently contains this. -/
def inputArity (x : Id) (comps : List Exp) : EvalM Nat :=
  if x == "Step" || x == "Step_pure" || x == "Step_read" || x == "Steps"
  then pure 1
  else if x == "Eval_expr" then pure 2
  else if x == "Module_ok" then pure 1
  -- Expand: deftype ~~ comptype (2.4-syntax.types.spectec) — functional
  -- unrolling, deftype in, comptype out
  else if x == "Expand" then pure 1
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

/-- Catch every error except `.fuel`, which must stay loud. Used only
around engine-level fallback attempts (rewriteCalls) where failure means
"stays symbolic → visible stuck downstream", never a silent wrong answer. -/
def catchNonFuel (m : EvalM α) (h : Unit → EvalM α) : EvalM α :=
  fun st =>
    match m st with
    | .error .fuel => .error .fuel
    | .error _ => h () st
    | r => r

/-- Three-valued premise-check result (audit dim2-4/dim2-5, verified
V3): `unknown` (undecidable) is distinct from `fail` (definitively
false). eval.ml distinguishes them at clause level (eval.ml:527-530:
`None` makes the WHOLE call irreducible; only `Some false` advances to
the next clause), and else/otherwise rules require definitive failure
of their earlier siblings. -/
inductive PremsRes where
  | ok (s : Subst)
  | fail
  | unknown

/-- Split a conclusion expression into its mixop components.
Relation conclusions are tuples of the mixop's arity (or a single
component for arity 1). -/
def components (e : Exp) : List Exp :=
  match e.it with
  | .tupE es => es
  | _ => [e]

mutual

/-- Check premises under `s`; RulePr recurses into `derive`.
Mirrors the reducePrems threading (union of accumulated substs).
`visited` is the derivation-cycle guard (see `derive`).

WORKLIST DEFERRAL (engine-level, logged): the spec writes premise
conjunctions in non-executable order — $allocmodule's "forward guess"
(4.4-execution.modules.spectec:121-133) passes `moduleinst` to
$allocfuncs premises BEFORE the premise that defines it; upstream's
il2al animation pass reorders premises for executability. Here an
undecidable premise is DEFERRED and retried after later premises extend
the substitution; rounds continue while progress is made. Equation order
within a conjunction is semantically free, so this changes evaluation
order only. `deferred`/`prog` are the worklist state; external callers
pass `[] false`. -/
def checkPrems (env : Env) (fuel : Nat) (assumed : List Id)
    (visited : List (Id × List Exp)) (s : Subst)
    (prems : List Prem) (deferred : List Prem) (prog : Bool) :
    EvalM PremsRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prems with
    | [] =>
      if deferred.isEmpty then pure (.ok s)
      else if prog then checkPrems env n assumed visited s deferred [] false
      -- exhausted deferral: the surviving premises are undecidable
      -- (every deferred premise still carries free variables), NOT
      -- definitively false (audit dim2-5)
      else pure .unknown
    | prem :: rest => do
      let ok := fun (s' : Subst) =>
        checkPrems env n assumed visited s' rest deferred true
      -- defer only when free variables remain (see hasVarPrem); a
      -- CLOSED undecidable premise is UNKNOWN, not false (audit
      -- dim2-5 corrected the earlier fail here)
      let defer := fun (pr : Prem) =>
        if hasVarPrem pr then
          checkPrems env n assumed visited s rest (deferred ++ [prem]) prog
        else pure .unknown
      let prem' ← liftS (Subst.substPremsOpt s [prem])
      let prem' := prem'.headD prem
      match prem' with
      | .rulePr x _args _op e => do
        -- HARNESS BOUNDARY: assumed validation relations (see
        -- evalCallRel doc + arc log) — satisfied without output binding;
        -- unbound outputs surface as visible stuck, never wrong answers
        if assumed.contains x then ok s else do
        -- premise components: bound prefix = inputs, unbound suffix = outs
        let comps := components e
        let (ps, mixop, _t, rules) ← match env.findRel? x with
          | some d => pure d
          | none => err s!"undeclared relation {x}"
        let _ := ps
        let k ← inputArity x comps
        let ins ← (comps.take k).mapM (fun c => reduceExpRel env n assumed c)
        let dres ← derive env n assumed visited x mixop rules ins k
        match dres with
        | .noRule =>
          -- CLOSED judgment with an exhaustive no-rule search is a
          -- definitive failure within engine semantics; with free
          -- variables it may become derivable after later bindings
          if hasVarPrem prem' then defer prem' else pure .fail
        | .stuck _ =>
          -- internal difficulty, not falsity: undecidable
          if hasVarPrem prem' then defer prem' else pure .unknown
        | .ok outs =>
          -- bind output patterns against derived outputs. NOTE the
          -- first-match/single-output limitation documented at
          -- `derive`: a mismatch here is treated as definitive
          let r ← (outs.zip (comps.drop k)).foldlM
            (fun (acc : Option Subst) cp => do
              match acc with
              | none => pure none
              | some sA =>
                catchIrred (matchExp' env n sA cp.1 cp.2)
                  (fun _ => pure none))
            (some s)
          match r with
          | none => pure .fail
          | some s' => ok s'
      | .ifPr e => do
        let er ← reduceExpRel env n assumed e
        match er.it with
        | .boolE true => ok s
        | .boolE false => pure .fail
        | .cmpE .eq _ a b => do
          -- BINDING equation (`-- if x = pattern …`): upstream's middlend
          -- rewrites these to `let` before AL (let-intro pass); our raw
          -- IL keeps them, so an undecidable equality is executed as a
          -- pattern match, either orientation. A match whose bindings
          -- still contain FREE VARIABLES is not a ground solution — it
          -- must wait for the premises that define those variables
          -- ($allocmodule's forward guess): defer it (engine-level rule,
          -- logged).
          let ground := fun (s' : Subst) =>
            s'.varid.entries.all (fun p => !hasVarExp p.2)
          -- track Irred: any Irred involvement makes the equation
          -- UNDECIDABLE; a no-match WITHOUT Irred on closed, fully
          -- reduced values is definite inequality (audit dim2-5)
          let (r1, irr1) ← catchIrred
            (do pure ((← matchExp env n Subst.empty a b), false))
            (fun _ => pure (none, true))
          match r1 with
          | some s' =>
            if ground s' then ok (Subst.union s s') else defer prem'
          | none => do
            let (r2, irr2) ← catchIrred
              (do pure ((← matchExp env n Subst.empty b a), false))
              (fun _ => pure (none, true))
            match r2 with
            | some s' =>
              if ground s' then ok (Subst.union s s') else defer prem'
            | none =>
              if !irr1 && !irr2
                  && !hasVarExp a && !hasVarExp b
                  && isNormalExp a && isNormalExp b then
                pure .fail
              else defer prem'
        | _ => defer prem'
      | .elsePr => ok s
      | .letPr _ e1 e2 => do
        let r ← catchIrred
          (do
            match ← matchExp env n Subst.empty e2 e1 with
            | some s' => pure (some s')
            | none => pure none)
          (fun _ => pure none)
        match r with
        | none => defer prem'
        | some s' => ok (Subst.union s s')
      | .iterPr inner _ => do
        -- iterated assumed-relation premises are likewise satisfied
        let rec innermost : Prem → Prem
          | .iterPr p _ => innermost p
          | p => p
        match innermost inner with
        | .rulePr x _ _ _ =>
          if assumed.contains x then ok s
          else do
            match ← reducePrem env n prem' with
            | .yes s' => ok (Subst.union s s')
            | .no => pure .fail
            | .unknown => defer prem'
        | _ => do
          match ← reducePrem env n prem' with
          | .yes s' => ok (Subst.union s s')
          | .no => pure .fail
          | .unknown => defer prem'
      | .negPr _ => do
        -- reuse Eval's premise reduction (handles Iter/Neg over the
        -- non-RulePr premise classes)
        match ← reducePrem env n prem' with
        | .yes s' => ok (Subst.union s s')
        | .no => pure .fail
        | .unknown => defer prem'



/-- Derive one step of relation `x` with `k` ground inputs. Rules tried
in spec order; sequence-split fallback for CatE-chain conclusions.
`visited` refuses a sub-derivation of the IDENTICAL judgment — same
relation, same `k` INPUT components — which is what makes context rules
like Step/ctxt-instrs (whose Step premise precedes the ≠eps guard)
terminate on empty sequences. LIMITATION (audit dim2-2/V8): for
MULTI-OUTPUT relations this refusal is NOT semantically exact — a
subsumption rule like Ref_ok/sub (4.1-execution.values.spectec:65-69)
legitimately derives the same inputs with a DIFFERENT output via a
same-input premise, which the guard refuses; such relations are
under-derived. Currently contained: no multi-output self-subsuming
relation is registered in `inputArity` (it fails closed), and the
warning there gates future registrations. The guard is a termination
device, not an exact LFP oracle. -/
def derive (env : Env) (fuel : Nat) (assumed : List Id)
    (visited : List (Id × List Exp))
    (x : Id) (_mixop : Mixop)
    (rules : List Rule) (ins : List Exp) (k : Nat) : EvalM DeriveRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    -- memoized (Fresh.St.deriveCache; soundness argued there). The
    -- cycle-guard check must PRECEDE the cache lookup: a refusal is
    -- path-local and must not be cached.
    let key := (x, ins)
    if visited.any (fun (y, ys) =>
        y == x && ys.length == ins.length
          && (ys.zip ins).all (fun (a, b) => eqExp a b)) then
      pure .noRule
    else
    match (← get).deriveCache.get? key with
    | some (.ok outs) => pure (.ok outs)
    | some .noRule => pure .noRule
    | some (.stuck m) => pure (.stuck m)
    | none => do
      let res ← deriveCore env n assumed visited x _mixop rules ins k
      -- INSERT only refusal-free computations (empty visited context;
      -- see the invariant at Fresh.St.deriveCache — audit dim3-F1/V10:
      -- results computed under a non-empty visited set can carry
      -- transitive cycle-refusal contamination). Lookups above remain
      -- unconditional: a cached entry is the guard-free result.
      if visited.isEmpty then
        let resC : Fresh.DeriveResC := match res with
          | .ok outs => .ok outs
          | .noRule => .noRule
          | .stuck m => .stuck m
        -- epoch flush bounds memory (see callCache note)
        modify (fun st =>
          let dc := if st.deriveCache.size > 100000 then {} else st.deriveCache
          { st with deriveCache := dc.insert key resC })
      pure res

/-- `sawUnknown`: an earlier rule in this scan had UNDECIDABLE premises.
An `elsePr`-carrying (otherwise) rule may then NOT fire — otherwise
semantics require definitive failure of the earlier siblings (audit
dim2-5); the scan returns a visible `.stuck` instead. Rules without
`elsePr` are justified by their own premises and may still be tried. -/
def deriveCore (env : Env) (fuel : Nat) (assumed : List Id)
    (visited : List (Id × List Exp))
    (x : Id) (_mixop : Mixop)
    (rules : List Rule) (ins : List Exp) (k : Nat)
    (sawUnknown : Bool := false) : EvalM DeriveRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    if visited.any (fun (y, ys) =>
        y == x && ys.length == ins.length
          && (ys.zip ins).all (fun (a, b) => eqExp a b)) then
      pure .noRule
    else if x == "Steps" then
      -- CLOSURE convention (engine-level, logged): Steps is the
      -- reflexive-transitive closure of Step (steps-refl/steps-trans,
      -- 4.3-execution.instructions.spectec); generic first-match search
      -- would stop at the reflexive rule. Step is deterministic, so the
      -- maximal chain is canonical: iterate Step to exhaustion.
      match ins with
      | [cfg] => stepsClosure env n assumed visited cfg
      | _ => err "Steps: expected a single config input"
    else
    let visited := (x, ins) :: visited
    match rules with
    | [] => pure .noRule
    | .mk _rname _ _qs _op concl prems :: rest => do
      let comps := components concl
      if comps.length < k then
        err s!"relation {x}: conclusion arity below input count"
      else do
        -- otherwise-rule gating (see docstring)
        if sawUnknown && prems.any (fun pr => match pr with
            | .elsePr => true | _ => false) then
          pure (.stuck s!"relation {x}: undecidable earlier rule blocks otherwise-rule {_rname}")
        else do
        let pats := comps.take k
        -- match each input component (sequence-split fallback for
        -- CatE-chain patterns over concrete lists: context rules)
        -- inputs matched CPS-style: premises are the continuation, so
        -- premise failure backtracks into other sequence splits.
        -- checkPrems' three-valued result is squeezed through the
        -- Option-typed enumeration via the Fresh.St.premsUnknown flag
        -- (saved/reset around the attempt; nested derives save/restore
        -- their own use, so the read below sees only THIS rule's
        -- continuation outcomes)
        let saved := (← get).premsUnknown
        modify (fun st => { st with premsUnknown := false })
        let mi ← matchInputsK env n Subst.empty (ins.zip pats)
          (fun s => do
            match ← checkPrems env n assumed visited s prems [] false with
            | .ok s' => pure (some s')
            | .fail => pure none
            | .unknown => do
              modify (fun st => { st with premsUnknown := true })
              pure none)
        let ruleUnknown := (← get).premsUnknown
        modify (fun st => { st with premsUnknown := saved })
        match mi with
        | none =>
          deriveCore env n assumed visited.tail x _mixop rest ins k
            (sawUnknown || ruleUnknown)
        | some s' => do
          -- premises already checked (they are the CPS continuation)
          let outs ← (comps.drop k).mapM (fun c => do
            reduceExpRel env n assumed (← liftS (Subst.substExpOpt s' c)))
          pure (.ok outs)

/-- Iterate `Step` from a configuration to exhaustion (see the Steps
closure convention in `derive`). -/
def stepsClosure (env : Env) (fuel : Nat) (assumed : List Id)
    (visited : List (Id × List Exp)) (cfg : Exp) : EvalM DeriveRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let (_, mixop, _, rules) ← match env.findRel? "Step" with
      | some d => pure d
      | none => err "relation Step not found"
    match ← derive env n assumed visited "Step" mixop rules [cfg] 1 with
    | .ok [cfg'] => stepsClosure env n assumed visited cfg'
    | .ok _ => err "Step produced unexpected arity"
    | .noRule => pure (.ok [cfg])
    | .stuck m => pure (.stuck m)

/-- Reduce, then evaluate residual rel-premised calls, then re-reduce
(the surrounding structure — `proj`, `cat`, … — over freshly produced
values). -/
def reduceExpRel (env : Env) (fuel : Nat) (assumed : List Id) (e : Exp) :
    EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let e1 ← reduceExp env n e
    let e2 ← rewriteCalls env n assumed e1
    reduceExp env n e2

/-- Innermost-first: evaluate residual `CallE` nodes via the rule engine.
Functions whose clauses carry RELATION premises ($evalglobals,
$evalexprs, …) are opaque to Eval.reduceExpCall (mirrors eval.ml:543
reduce_prem RulePr → unknown); this rewrites them with evalCallRelA. A
call that still fails stays symbolic (visible stuck downstream). -/
def rewriteCalls (env : Env) (fuel : Nat) (assumed : List Id) (e : Exp) :
    EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match e with
    | .mk it note => do
      let it' ← rewriteCalls' env n assumed it
      match it' with
      | .callE x args =>
        catchNonFuel
          (do
            let r ← evalCallRelA env n assumed x args note
            -- the produced body may expose further rel-calls
            rewriteCalls env n assumed r)
          (fun _ => pure (Exp.mk it' note))
      | _ => pure (Exp.mk it' note)

def rewriteCalls' (env : Env) (fuel : Nat) (assumed : List Id) :
    Exp' → EvalM Exp' :=
  fun it =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    let rw := rewriteCalls env n assumed
    match it with
    | .varE _ | .boolE _ | .numE _ | .textE _ => pure it
    | .unE op t e1 => do pure (.unE op t (← rw e1))
    | .binE op t e1 e2 => do pure (.binE op t (← rw e1) (← rw e2))
    | .cmpE op t e1 e2 => do pure (.cmpE op t (← rw e1) (← rw e2))
    | .tupE es => do pure (.tupE (← es.mapM rw))
    | .projE e1 i => do pure (.projE (← rw e1) i)
    | .caseE op e1 => do pure (.caseE op (← rw e1))
    | .uncaseE e1 op => do pure (.uncaseE (← rw e1) op)
    | .optE none => pure it
    | .optE (some e1) => do pure (.optE (some (← rw e1)))
    | .theE e1 => do pure (.theE (← rw e1))
    | .strE efs => do
      pure (.strE (← efs.mapM (fun f => match f with
        | .mk a e1 => do pure (ExpField.mk a (← rw e1)))))
    | .dotE e1 a => do pure (.dotE (← rw e1) a)
    | .compE e1 e2 => do pure (.compE (← rw e1) (← rw e2))
    | .listE es => do pure (.listE (← es.mapM rw))
    | .liftE e1 => do pure (.liftE (← rw e1))
    | .memE e1 e2 => do pure (.memE (← rw e1) (← rw e2))
    | .lenE e1 => do pure (.lenE (← rw e1))
    | .catE e1 e2 => do pure (.catE (← rw e1) (← rw e2))
    | .idxE e1 e2 => do pure (.idxE (← rw e1) (← rw e2))
    | .sliceE e1 e2 e3 => do pure (.sliceE (← rw e1) (← rw e2) (← rw e3))
    | .updE e1 p e2 => do pure (.updE (← rw e1) p (← rw e2))
    | .extE e1 p e2 => do pure (.extE (← rw e1) p (← rw e2))
    | .ifE e1 e2 e3 => do pure (.ifE (← rw e1) (← rw e2) (← rw e3))
    | .callE x args => do
      pure (.callE x (← args.mapM (fun a => match a with
        | .expA e1 => do pure (Arg.expA (← rw e1))
        | a => pure a)))
    | .iterE e1 (.mk iter xes) => do
      let xes' ← xes.mapM (fun d => match d with
        | .mk x ex => do pure (Dom.mk x (← rw ex)))
      pure (.iterE (← rw e1) (.mk iter xes'))
    | .cvtE e1 nt1 nt2 => do pure (.cvtE (← rw e1) nt1 nt2)
    | .subE e1 t1 t2 => do pure (.subE (← rw e1) t1 t2)

/-- Evaluate a function call whose clause premises may include RELATION
premises: reduceExpCall's premise handling can't derive relations; this
mirrors it with `checkPrems`. -/
def evalCallRelA (env : Env) (fuel : Nat) (assumed : List Id)
    (x : Id) (args : List Arg) (retT : Typ) : EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let (_, _, clauses) ← match env.findDef? x with
      | some d => pure d
      | none => Eval.err s!"undeclared definition {x}"
    let args' ← args.mapM (Eval.reduceArg env n)
    -- open-arg guard, EXECUTION-ONLY like the Eval.reduceExp CallE row
    -- (gated on Env.guardOpenCalls since f0afbcc's scoping; audit
    -- dim1-7/dim3-F6 caught this copy left unconditional)
    if env.guardOpenCalls && args'.any (fun a => match a with
        | .expA e1 => Eval.hasVarExp e1
        | _ => false) then
      Eval.err s!"entry call {x}: open arguments"
    else
    let _ := retT
    evalCallClauses env n assumed x args' clauses

def evalCallClauses (env : Env) (fuel : Nat) (assumed : List Id)
    (x : Id) (args' : List Arg) : List Clause → EvalM Exp :=
  fun clauses =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match clauses with
    | [] => Eval.err s!"entry call {x}: no clause applies"
    | .mk _ _ pats body prems :: rest => do
      -- mirror eval.ml:527-530 exactly: undecidable premises make the
      -- WHOLE call irreducible (`None -> None`); only definitive
      -- premise failure (`Some false`) advances to the next clause
      -- (audit dim2-4/V3). The `.error` thrown for unknown passes
      -- through catchIrred; execution-side callers keep the call
      -- symbolic (rewriteCalls catchNonFuel) or surface it visibly.
      let r ← Eval.catchIrred
        (do
          match ← Eval.matchListM (fun s a b => Eval.matchArg env n s a b)
              Subst.empty args' pats with
          | none => pure (some none)
          | some s =>
            match ← checkPrems env n assumed [] s prems [] false with
            | .fail => pure (some none)
            | .unknown => pure none
            | .ok s' => do
              pure (some (some (← Eval.reduceExp env n
                (← Eval.liftS (Subst.substExpOpt s' body))))))
        (fun _ => pure (some none))
      match r with
      | some (some e) => pure e
      | some none => evalCallClauses env n assumed x args' rest
      | none => Eval.err s!"entry call {x}: undecidable premises"

end

/-- Entry-call form of `evalCallRelA` over plain expression arguments. -/
def evalCallRel (env : Env) (fuel : Nat) (assumed : List Id)
    (x : Id) (args : List Exp) (retT : Typ) : EvalM Exp :=
  evalCallRelA env fuel assumed x (args.map .expA) retT

end Rel

end SpecTecLean.Il
