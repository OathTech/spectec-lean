import SpecTecLean.Il.Ast
import SpecTecLean.XlOps
import SpecTecLean.Il.Free
import SpecTecLean.Il.Eq
import SpecTecLean.Il.Env
import SpecTecLean.Il.Subst
import SpecTecLean.Il.ToSexpr
/-!
Type/expression reduction, matching, equivalence, subtyping — mirroring
`deps/spectec/spectec/src/il/eval.ml` in full (spectec @ acc6e834 +
vendored patch).

Structure of the mirror (all logged as arc-2 decisions):

- **Fuel.** eval.ml's recursion is genuinely non-structural (alias
  unfolding via the environment, function-clause bodies, `sub_typ`'s
  assumption set). Every mutual function takes a `Nat` fuel argument,
  decremented at EVERY recursive call; exhaustion throws `.fuel` — a loud
  sentinel, never a wrong answer (the cerberus fuel-totalize pattern).
- **Errors.** OCaml uses exceptions with distinct catch sites: `Irred`
  (eval.ml:20; caught at reduce_typ_app' / reduce_exp_call / the
  CompE-StrE `try`), `Failure` (`failwith` in as_opt_exp/as_list_exp;
  caught only by that `try`, eval.ml:271-275), and `Error.Error`
  (validation errors, never caught here). Mirrored as
  `EvalErr.irred/.failure/.error` with catch combinators at exactly those
  sites; `.fuel` is never caught.
- **`assume_coherent_matches`** (eval.ml:22) is FIXED to `true` (the
  toolchain default; the `false` mode is middlend-only, out of scope).
- **Real arithmetic fails closed** before the numeric tables (XlOps).
- OCaml polymorphic (in)equality guards on reduction progress
  (eval.ml:986,990,993,1161,1164) compare regions too; mirrored as
  `!(eqTyp …)` — stronger stopping condition, backstopped by fuel.
- Debug-only asserts (eval.ml:521,741) are not mirrored.
-/

namespace SpecTecLean.Il

open SpecTecLean (Sexpr)
open SpecTecLean.Xl (Atom Mixop)

inductive EvalErr where
  | irred
  | failure (msg : String)
  | error (msg : String)
  | fuel
deriving Repr, BEq

abbrev EvalM := StateT Fresh.St (Except EvalErr)

namespace Eval

/-- Lift substitution (its String errors are validation-class). -/
def liftS (m : SubstM α) : EvalM α :=
  fun st =>
    match m st with
    | .ok r => .ok r
    | .error e => .error (.error e)

/-- Catch `.irred` only. -/
def catchIrred (m : EvalM α) (h : Unit → EvalM α) : EvalM α :=
  fun st =>
    match m st with
    | .error .irred => h () st
    | r => r

/-- Catch `.irred` and `.failure` (eval.ml:271-275). -/
def catchIrredFailure (m : EvalM α) (h : Unit → EvalM α) : EvalM α :=
  fun st =>
    match m st with
    | .error .irred => h () st
    | .error (.failure _) => h () st
    | r => r

def err (msg : String) : EvalM α := throw (.error msg)

/-- eval.ml:28 `unordered`. -/
def unordered (s1 s2 : IdSet) : Bool :=
  !(IdSet.subset s1 s2 || IdSet.subset s2 s1)

/-- eval.ml:31-40. -/
def ofBoolExp : Exp' → Option Bool
  | .boolE b => some b
  | _ => none

def ofNumExp : Exp' → Option Num
  | .numE n => some n
  | _ => none

/-- eval.ml:42-50 (`failwith` → `.failure`). -/
def asOptExp (e : Exp) : EvalM (Option Exp) :=
  match e.it with
  | .optE eo => pure eo
  | _ => throw (.failure "as_opt_exp")

def asListExp (e : Exp) : EvalM (List Exp) :=
  match e.it with
  | .listE es => pure es
  | _ => throw (.failure "as_list_exp")

/-- eval.ml:154-159 `is_head_normal_exp`. -/
def isHeadNormalExp (e : Exp) : Bool :=
  match e with | .mk it _ => go it
where
  go : Exp' → Bool
    | .boolE _ | .numE _ | .textE _
    | .optE _ | .listE _ | .tupE _ | .caseE _ _ | .strE _ => true
    | .subE (.mk it _) _ _ => go it
    | _ => false

mutual
/-- eval.ml:161-168 `is_normal_exp`. -/
def isNormalExp (e : Exp) : Bool :=
  match e with
  | .mk it _ => isNormalExp' it
  termination_by 2 * sizeOf e

def isNormalExp' : Exp' → Bool
  | .boolE _ | .numE _ | .textE _ => true
  | .listE es => es.attach.all (fun ⟨e1, _⟩ => isNormalExp e1)
  | .tupE es => es.attach.all (fun ⟨e1, _⟩ => isNormalExp e1)
  | .optE none => true
  | .optE (some e1) => isNormalExp e1
  | .caseE _ e1 => isNormalExp e1
  | .subE e1 _ _ => isNormalExp e1
  | .strE efs =>
    efs.attach.all (fun ⟨f, _⟩ => match f with | .mk _ e1 => isNormalExp e1)
  | _ => false
  termination_by it => 2 * sizeOf it + 1
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
      | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; simp at this; omega)
end

mutual
/-- `isNormalExp` minus `subE`: the reduce fast path must NOT skip a
term containing subsumption wrappers — reduce is what ERASES them
(eval.ml:430-433); treating `subE(value)` as done leaves wrappers in
bound values and breaks matching. -/
def isPureNormalExp (e : Exp) : Bool :=
  match e with
  | .mk it _ => isPureNormalExp' it
  termination_by 2 * sizeOf e

def isPureNormalExp' : Exp' → Bool
  | .boolE _ | .numE _ | .textE _ => true
  | .listE es => es.attach.all (fun ⟨e1, _⟩ => isPureNormalExp e1)
  | .tupE es => es.attach.all (fun ⟨e1, _⟩ => isPureNormalExp e1)
  | .optE none => true
  | .optE (some e1) => isPureNormalExp e1
  | .caseE _ e1 => isPureNormalExp e1
  | .strE efs =>
    efs.attach.all (fun ⟨f, _⟩ => match f with | .mk _ e1 => isPureNormalExp e1)
  | _ => false
  termination_by it => 2 * sizeOf it + 1
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
      | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; simp at this; omega)
end

mutual
/-- Does the expression contain any variable occurrence? Deferral is
useful ONLY for premises with free variables — a closed premise's
outcome cannot change under a larger substitution. -/
def hasVarExp (e : Exp) : Bool :=
  match e with
  | .mk it _ => hasVarExp' it
  termination_by 2 * sizeOf e

def hasVarExp' : Exp' → Bool
  | .varE _ => true
  | .boolE _ | .numE _ | .textE _ => false
  | .unE _ _ e1 => hasVarExp e1
  | .projE e1 _ => hasVarExp e1
  | .caseE _ e1 => hasVarExp e1
  | .uncaseE e1 _ => hasVarExp e1
  | .theE e1 => hasVarExp e1
  | .dotE e1 _ => hasVarExp e1
  | .liftE e1 => hasVarExp e1
  | .lenE e1 => hasVarExp e1
  | .cvtE e1 _ _ => hasVarExp e1
  | .subE e1 _ _ => hasVarExp e1
  | .binE _ _ e1 e2 => hasVarExp e1 || hasVarExp e2
  | .cmpE _ _ e1 e2 => hasVarExp e1 || hasVarExp e2
  | .compE e1 e2 => hasVarExp e1 || hasVarExp e2
  | .memE e1 e2 => hasVarExp e1 || hasVarExp e2
  | .catE e1 e2 => hasVarExp e1 || hasVarExp e2
  | .idxE e1 e2 => hasVarExp e1 || hasVarExp e2
  | .sliceE e1 e2 e3 => hasVarExp e1 || hasVarExp e2 || hasVarExp e3
  | .ifE e1 e2 e3 => hasVarExp e1 || hasVarExp e2 || hasVarExp e3
  | .updE e1 _ e2 => hasVarExp e1 || hasVarExp e2
  | .extE e1 _ e2 => hasVarExp e1 || hasVarExp e2
  | .tupE es => es.attach.any (fun ⟨e1, _⟩ => hasVarExp e1)
  | .listE es => es.attach.any (fun ⟨e1, _⟩ => hasVarExp e1)
  | .optE none => false
  | .optE (some e1) => hasVarExp e1
  | .strE efs =>
    efs.attach.any (fun ⟨f, _⟩ => match f with | .mk _ e1 => hasVarExp e1)
  | .callE _ args => args.attach.any (fun ⟨a, _⟩ => match a with
      | .expA e1 => hasVarExp e1
      | _ => false)
  | .iterE e1 (.mk _ xes) =>
    hasVarExp e1 || xes.attach.any (fun ⟨d, _⟩ => match d with
      | .mk _ ex => hasVarExp ex)
  termination_by it => 2 * sizeOf it + 1
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
      | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; simp at this; omega)
end

def hasVarPrem : Prem → Bool
  | .rulePr _ _ _ e => hasVarExp e
  | .ifPr e => hasVarExp e
  | .elsePr => false
  | .letPr _ e1 e2 => hasVarExp e1 || hasVarExp e2
  | .iterPr p _ => hasVarPrem p
  | .negPr p => hasVarPrem p

/-- Fail-closed pre-check: real arithmetic unsupported (header). -/
def checkNoReal (n : Num) : EvalM Unit :=
  match n with
  | .real _ =>
    err "real arithmetic unsupported (fail-closed; zero corpus coverage)"
  | _ => pure ()

/-- Rebuild an Exp keeping a note (`$> e` in OCaml). -/
@[inline] def withNote (it : Exp') (e : Exp) : Exp := .mk it e.note

/-- eval.ml:61-67 `match_list` (generic; recursion is on the lists, the
callback carries its own fuel). -/
def matchListM (f : Subst → α → α → EvalM (Option Subst)) (s : Subst) :
    List α → List α → EvalM (Option Subst)
  | [], [] => pure (some s)
  | x1 :: xs1, x2 :: xs2 => do
    match ← f s x1 x2 with
    | none => pure none
    | some s' => matchListM f (Subst.union s s') xs1 xs2
  | _, _ => pure none

/-- eval.ml:69-70 `equiv_list` (generic). -/
def equivListM (f : α → α → EvalM Bool) : List α → List α → EvalM Bool
  | [], [] => pure true
  | x1 :: xs1, x2 :: xs2 => do
    if ← f x1 x2 then equivListM f xs1 xs2 else pure false
  | _, _ => pure false

/-- eval.ml:1127-1131 `find_field`/`find_case` (Option form). -/
def findFieldOpt (tfs : List TypField) (atom : Atom) :
    Option (Typ × List Param × List Prem) :=
  match tfs.find? (fun f => match f with | .mk a _ _ _ => eqAtom a atom) with
  | some (.mk _ t qs prems) => some (t, qs, prems)
  | none => none

def findCaseOpt (tcs : List TypCase) (op : Mixop) :
    Option (Typ × List Param × List Prem) :=
  match tcs.find? (fun c => match c with | .mk o _ _ _ => eqMixop o op) with
  | some (.mk _ t qs prems) => some (t, qs, prems)
  | none => none

/-- eval.ml:139-149 (erroring form). -/
def findTypfield (tfs : List TypField) (atom : Atom) :
    EvalM (Typ × List Param × List Prem) :=
  match findFieldOpt tfs atom with
  | some r => pure r
  | none => err s!"unbound field `{XlPrint.atomToString atom}`"

def findTypcase (tcs : List TypCase) (op : Mixop) :
    EvalM (Typ × List Param × List Prem) :=
  match findCaseOpt tcs op with
  | some r => pure r
  | none => err s!"unknown case `{XlPrint.mixopToString op}`"

/-- eval.ml:1171-1172 `atoms`/`mixops` (string-keyed sets). -/
def atomsSet (tfs : List TypField) : IdSet :=
  (tfs.map (fun f => match f with
    | .mk a _ _ _ => XlPrint.atomToString a)).foldl
    (fun s x => IdSet.union s [x]) []

def mixopsSet (tcs : List TypCase) : IdSet :=
  (tcs.map (fun c => match c with
    | .mk o _ _ _ => XlPrint.mixopToString o)).foldl
    (fun s x => IdSet.union s [x]) []

/-- eval.ml:541 result of premise reduction. -/
inductive PremRes where
  | yes (s : Subst)   -- `True s
  | no                -- `False
  | unknown           -- `None
deriving Inhabited

mutual

/-- eval.ml:75-87 `reduce_typ` (weak-head). -/
def reduceTyp (env : Env) (fuel : Nat) (t : Typ) : EvalM Typ :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match t with
    | .varT x args => do
      let args' ← args.mapM (reduceArg env n)
      match ← reduceTypApp' env n x args' (env.findTyp? x) with
      | some (.aliasT t') => reduceTyp env n t'
      | _ => pure (.varT x args')
    | t => pure t

/-- eval.ml:89-97 `reduce_typdef`. -/
def reduceTypdef (env : Env) (fuel : Nat) (t : Typ) : EvalM DefTyp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let t' ← reduceTyp env n t
    match t' with
    | .varT x args =>
      match ← reduceTypApp env n x args with
      | some dt => pure dt
      | none => pure (.aliasT t)
    | _ => pure (.aliasT t)

/-- eval.ml:99-104 `reduce_typ_app`. -/
def reduceTypApp (env : Env) (fuel : Nat) (x : Id) (args : List Arg) :
    EvalM (Option DefTyp) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let args' ← args.mapM (reduceArg env n)
    reduceTypApp' env n x args' (env.findTyp? x)

/-- eval.ml:106-122 `reduce_typ_app'` (assume_coherent_matches = true:
an undefined partial-type instance yields `none`; an Irred match skips
to the next instance). -/
def reduceTypApp' (env : Env) (fuel : Nat) (x : Id) (args : List Arg) :
    Option TypDef → EvalM (Option DefTyp) :=
  fun td =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match td with
    | none => pure none  -- id is a type parameter
    | some (_, []) => pure none  -- partial type: no instance (flag=true)
    | some (ps, .mk _ _ args' dt :: insts') =>
      catchIrred
        (do
          match ← matchListM (fun s a1 a2 => matchArg env n s a1 a2)
              Subst.empty args args' with
          | none => reduceTypApp' env n x args (some (ps, insts'))
          | some s => do pure (some (← liftS (Subst.substDeftypOpt s dt))))
        (fun _ => reduceTypApp' env n x args (some (ps, insts')))

/-- eval.ml:125-137 `as_struct_typ`/`as_variant_typ`. -/
def asStructTyp (env : Env) (fuel : Nat) (t : Typ) : EvalM (List TypField) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match ← reduceTypdef env n t with
    | .structT tfs => pure tfs
    | _ => err "expression's type is not a record"

def asVariantTyp (env : Env) (fuel : Nat) (t : Typ) : EvalM (List TypCase) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match ← reduceTypdef env n t with
    | .variantT tcs => pure tcs
    | _ => err "expression's type is not a variant"

/-- eval.ml:170-442 `reduce_exp`. -/
def reduceExp (env : Env) (fuel : Nat) (e : Exp) : EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    -- PERF DIVERGENCE (logged, arc-2 stage 7): eval.ml re-checks case
    -- premises on EVERY reduce of every CaseE (eval.ml:387-393) — fine
    -- for middlend-sized terms, quadratic on value-sized terms (stores,
    -- names). Fully-normal expressions are returned as-is; the skipped
    -- effect is the Irred side-channel for ill-formed-but-normal case
    -- values, which well-typed closed execution does not produce.
    if isPureNormalExp e then pure e else
    match e.it with
    | .varE _ | .boolE _ | .numE _ | .textE _ => pure e
    | .unE op ot e1 => do
      let e1' ← reduceExp env n e1
      match op, e1'.it with
      | .not, .boolE b1 => pure (withNote (.boolE (BoolOps.un .not b1)) e)
      | op, .numE n1 => do
        checkNoReal n1
        match NumOps.un op n1 with
        | some v => pure (withNote (.numE v) e)
        | none => pure (withNote (.unE op ot e1') e)
      | .not, .unE .not _ e11' => pure e11'
      | .minus, .unE .minus _ e11' => pure e11'
      | op, _ => pure (withNote (.unE op ot e1') e)
    | .binE op ot e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      match op with
      | .and | .or | .impl | .equiv =>
        match BoolOps.binPartial op e1'.it e2'.it ofBoolExp .boolE with
        | none => pure (withNote (.binE op ot e1' e2') e)
        | some it => pure (withNote it e)
      | _ => do
        if let some v := ofNumExp e1'.it then checkNoReal v
        if let some v := ofNumExp e2'.it then checkNoReal v
        match NumOps.binPartial op e1'.it e2'.it ofNumExp .numE with
        | none => pure (withNote (.binE op ot e1' e2') e)
        | some it => pure (withNote it e)
    | .cmpE op ot e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      match op, e1'.it, e2'.it with
      | .eq, _, _ =>
        if isNormalExp e1' && isNormalExp e2' then
          pure (withNote (.boolE (eqExp e1' e2')) e)
        else pure (withNote (.cmpE op ot e1' e2') e)
      | .ne, _, _ =>
        if isNormalExp e1' && isNormalExp e2' then
          pure (withNote (.boolE (!eqExp e1' e2')) e)
        else pure (withNote (.cmpE op ot e1' e2') e)
      | op, .numE n1, .numE n2 => do
        checkNoReal n1; checkNoReal n2
        match NumOps.cmp op n1 n2 with
        | some b => pure (withNote (.boolE b) e)
        | none => pure (withNote (.cmpE op ot e1' e2') e)
      | _, _, _ => pure (withNote (.cmpE op ot e1' e2') e)
    | .idxE e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      match e1'.it, e2'.it with
      | .listE es, .numE (.nat i) =>
        if h : i < es.length then pure es[i]
        else pure (withNote (.idxE e1' e2') e)
      | _, _ => pure (withNote (.idxE e1' e2') e)
    | .sliceE e1 e2 e3 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      let e3' ← reduceExp env n e3
      match e1'.it, e2'.it, e3'.it with
      | .listE es, .numE (.nat i), .numE (.nat len) =>
        -- eval.ml:230: guard is  i + n < length  (NOT ≤ — mirrored)
        if i + len < es.length then
          pure (withNote (.listE ((es.drop i).take len)) e)
        else pure (withNote (.sliceE e1' e2' e3') e)
      | _, _, _ => pure (withNote (.sliceE e1' e2' e3') e)
    | .updE e1 p e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      reducePath env n e1' p (fun e' p' =>
        match p'.it with
        | .rootP => pure e2'
        | _ => pure (withNote (.updE e' p' e2') e'))
    | .extE e1 p e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      reducePath env n e1' p (fun e' p' =>
        match p'.it with
        | .rootP => reduceExp env n (withNote (.catE e' e2') e')
        | _ => pure (withNote (.extE e' p' e2') e'))
    | .strE efs => do
      let tfs ← asStructTyp env n e.note
      let efs' ← efs.mapM (reduceExpfield env n tfs)
      pure (withNote (.strE efs') e)
    | .dotE e1 atom => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .strE efs =>
        match efs.find? (fun f => match f with | .mk a _ => eqAtom a atom) with
        | some (.mk _ e2) => pure e2
        | none => pure (withNote (.dotE e1' atom) e)
      | _ => pure (withNote (.dotE e1' atom) e)
    | .compE e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      match e1'.it, e2'.it with
      | .listE es1, .listE es2 => pure (withNote (.listE (es1 ++ es2)) e)
      | .optE none, .optE _ => pure (withNote e2'.it e)
      | .optE _, .optE none => pure (withNote e1'.it e)
      | .strE efs1, .strE efs2 =>
        if efs1.length != efs2.length then
          -- OCaml List.map2 raises Invalid_argument, NOT caught by the try
          err "CompE: record field arity mismatch"
        else
          catchIrredFailure
            (do
              let tfs ← asStructTyp env n e.note
              let merged ← (efs1.zip efs2).mapM (fun (f1, f2) =>
                match f1, f2 with
                | .mk a1 e1f, .mk a2 e2f => do
                  -- eval.ml:268 assert (Atom.eq): fail closed instead
                  if !eqAtom a1 a2 then
                    -- eval.ml:268 assert (uncaught upstream): crash-class
                    err "CompE: field order mismatch (assert upstream)"
                  else
                    reduceExp env n (withNote (.compE e1f e2f) e1f) >>=
                      fun e' => pure (ExpField.mk a1 e'))
              let efs' ← merged.mapM (fun f =>
                match f with
                | .mk a ef => reduceExpfield env n tfs (.mk a ef))
              pure (withNote (.strE efs') e))
            (fun _ => pure (withNote (.compE e1' e2') e))
      | _, _ => pure (withNote (.compE e1' e2') e)
    | .memE e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      match e2'.it with
      | .optE none => pure (withNote (.boolE false) e)
      | .optE (some e21) =>
        if eqExp e1' e21 then pure (withNote (.boolE true) e)
        else if isNormalExp e1' && isNormalExp e21 then
          pure (withNote (.boolE false) e)
        else pure (withNote (.memE e1' e2') e)
      | .listE [] => pure (withNote (.boolE false) e)
      | .listE es2 =>
        if es2.any (eqExp e1') then pure (withNote (.boolE true) e)
        else if isNormalExp e1' && es2.all isNormalExp then
          pure (withNote (.boolE false) e)
        else pure (withNote (.memE e1' e2') e)
      | _ => pure (withNote (.memE e1' e2') e)
    | .lenE e1 => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .listE es => pure (withNote (.numE (.nat es.length)) e)
      | _ => pure (withNote (.lenE e1') e)
    | .tupE es => do
      pure (withNote (.tupE (← es.mapM (reduceExp env n))) e)
    | .callE x args => do
      let args' ← args.mapM (reduceArg env n)
      -- OPEN-ARG GUARD (engine-level, logged): under the ground-solution
      -- policy a call result containing free variables is never
      -- accepted (binding-eqs defer instead), so evaluating open-arg
      -- calls is pure waste — and the symbolic attempts blow up
      -- (measured 53 GB on $allocfuncs with a free moduleinst). Keep
      -- the call symbolic; the worklist retries it once its arguments
      -- are ground. Any lost inline-then-match case surfaces as a
      -- visible stuck/unmatched row against the pinned baseline.
      if env.guardOpenCalls && args'.any (fun a => match a with
          | .expA e1 => hasVarExp e1
          | _ => false) then
        pure (withNote (.callE x args') e)
      else do
      let (_, _, clauses) ← match env.findDef? x with
        | some d => pure d
        | none => err s!"undeclared definition `{x}`"
      -- memoized (see Fresh.St.callCache)
      let key := (x, args')
      match (← get).callCache.get? key with
      | some cached =>
        match cached with
        | none => pure (withNote (.callE x args') e)
        | some e' => pure e'
      | none => do
        -- flag=true: an empty clause list falls through to the None case
        let r ← reduceExpCall env n x args' clauses
        -- epoch flush bounds memory (keys embed stores; an unbounded
        -- cache measured 8+ GB RSS on nop.wast)
        modify (fun st =>
          let cc := if st.callCache.size > 200000 then {} else st.callCache
          { st with callCache := cc.insert key r })
        match r with
        | none => pure (withNote (.callE x args') e)
        | some e' => pure e'
    | .iterE e1 (.mk iter xes) => do
      let e1' ← reduceExp env n e1
      let iter' ← reduceIter env n iter
      let xes' ← xes.mapM (fun d => match d with
        | .mk x ex => do pure (Dom.mk x (← reduceExp env n ex)))
      let ids := xes'.map (fun d => match d with | .mk x _ => x)
      let es' := xes'.map (fun d => match d with | .mk _ ex => ex)
      let isListN := match iter' with | .listN _ _ => true | _ => false
      if !(es'.all isHeadNormalExp) || (!isListN && es'.isEmpty) then
        pure (withNote (.iterE e1' (.mk iter' xes')) e)
      else
        match iter' with
        | .opt => do
          let eos' ← es'.mapM asOptExp
          if eos'.all Option.isNone then
            pure (withNote (.optE none) e)
          else if eos'.all Option.isSome then do
            let es1' := eos'.filterMap id
            let s := (ids.zip es1').foldl
              (fun s (x, ex) => Subst.addVarid s x ex) Subst.empty
            let body ← reduceExp env n (← liftS (Subst.substExpOpt s e1'))
            -- DELIBERATE DIVERGENCE from eval.ml:318-321, which returns
            -- the bare substituted body — element-typed where the IterE
            -- is opt-typed. That ill-typed form breaks later opt-pattern
            -- matching and TheE reduction; latent upstream (eval.ml never
            -- evaluates value-building clauses — il2al takes over there).
            -- We keep the value type-correct: wrap in `OptE (Some …)`.
            -- Candidate upstream report (TODO.md).
            pure (withNote (.optE (some body)) e)
          else
            pure (withNote (.iterE e1' (.mk iter' xes')) e)
        | .list | .list1 => do
          let len ← match es' with
            | e0 :: _ => do pure (← asListExp e0).length
            | [] => throw (.failure "as_list_exp")
          let isList := match iter' with | .list => true | _ => false
          if isList || len ≥ 1 then
            let en : Exp := .mk (.numE (.nat len)) (.numT .nat)
            reduceExp env n
              (withNote (.iterE e1' (.mk (.listN en none) xes')) e)
          else
            pure (withNote (.iterE e1' (.mk iter' xes')) e)
        | .listN lenE ido => do
          match lenE.it with
          | .numE (.nat len) => do
            let ess' ← es'.mapM asListExp
            if ess'.all (fun es => es.length == len) then do
              let inner ← (List.range len).mapM (fun i => do
                let esI' := ess'.map (fun es => es[i]!)
                let s := (ids.zip esI').foldl
                  (fun s (x, ex) => Subst.addVarid s x ex) Subst.empty
                let s' := match ido with
                  | none => s
                  | some idx =>
                    Subst.addVarid s idx (.mk (.numE (.nat i)) (.numT .nat))
                liftS (Subst.substExpOpt s' e1'))
              reduceExp env n (withNote (.listE inner) e)
            else
              pure (withNote (.iterE e1' (.mk iter' xes')) e)
          | _ => pure (withNote (.iterE e1' (.mk iter' xes')) e)
    | .projE e1 i => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .tupE es =>
        if h : i < es.length then pure es[i]
        else err "invalid tuple projection"
      | _ => pure (withNote (.projE e1' i) e)
    | .uncaseE e1 op => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .caseE _ e11' => pure e11'
      | _ => pure (withNote (.uncaseE e1' op) e)
    | .optE none => pure (withNote (.optE none) e)
    | .optE (some e1) => do
      pure (withNote (.optE (some (← reduceExp env n e1))) e)
    | .theE e1 => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .optE (some e11) => pure e11
      | _ => pure (withNote (.theE e1') e)
    | .listE es => do
      pure (withNote (.listE (← es.mapM (reduceExp env n))) e)
    | .liftE e1 => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .optE none => pure (withNote (.listE []) e)
      | .optE (some e11') => pure (withNote (.listE [e11']) e)
      | _ => pure (withNote (.liftE e1') e)
    | .catE e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      match e1'.it, e2'.it with
      | .listE es1, .listE es2 => pure (withNote (.listE (es1 ++ es2)) e)
      | .optE none, .optE _ => pure (withNote e2'.it e)
      | .optE _, .optE none => pure (withNote e1'.it e)
      | _, _ => pure (withNote (.catE e1' e2') e)
    | .caseE op e1 => do
      let e1' ← reduceExp env n e1
      let tcs ← asVariantTyp env n e.note
      let (_, _, prems) ← findTypcase tcs op
      match ← reducePrems env n Subst.empty prems with
      | .no => throw .irred
      | _ => pure (withNote (.caseE op e1') e)
    | .cvtE e1 nt1 nt2 => do
      if nt1 == .real || nt2 == .real then
        err "real arithmetic unsupported (fail-closed; zero corpus coverage)"
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .numE v => do
        checkNoReal v
        match NumOps.cvt nt2 v with
        | some v' => pure (withNote (.numE v') e)
        | none => pure (withNote (.cvtE e1' nt1 nt2) e)
      | _ => pure (withNote (.cvtE e1' nt1 nt2) e)
    | .subE e1 t1 t2 => do
      let e1' ← reduceExp env n e1
      let t1' ← reduceTyp env n t1
      let t2' ← reduceTyp env n t2
      if ← equivTyp env n t1' t2' then pure e1'
      else
        match e1'.it with
        | .subE e11' t11' _ =>
          reduceExp env n (withNote (.subE e11' t11' t2') e)
        | .tupE es' =>
          match t1, t2 with
          | .tupT xts1, .tupT xts2 =>
            if es'.length != xts1.length || xts1.length != xts2.length then
              pure (withNote (.subE e1' t1' t2') e)
            else do
              -- eval.ml:413-429 (the fold's None branch is dead: seed is
              -- Some and every step returns Some; lengths pre-checked)
              let (_, _, resRev) ← (es'.zip (xts1.zip xts2)).foldlM
                (fun (st : Subst × Subst × List Exp) pr => do
                  let (s1, s2, res) := st
                  let (eI, b1, b2) := pr
                  match b1, b2 with
                  | .mk x1I t1I, .mk x2I t2I => do
                    let t1I' ← liftS (Subst.substTypOpt s1 t1I)
                    let t2I' ← liftS (Subst.substTypOpt s2 t2I)
                    let eI' ← reduceExp env n (Exp.mk (.subE eI t1I' t2I') t2I')
                    pure (Subst.addVarid s1 x1I eI, Subst.addVarid s2 x2I eI,
                          eI' :: res))
                (Subst.empty, Subst.empty, ([] : List Exp))
              pure (withNote (.tupE resRev.reverse) e)
          | _, _ => pure (withNote (.subE e1' t1' t2') e)
        | _ =>
          if isHeadNormalExp e1' then
            pure (Exp.mk e1'.it e.note)
          else pure (withNote (.subE e1' t1' t2') e)
    | .ifE e1 e2 e3 => do
      let e1' ← reduceExp env n e1
      match e1'.it with
      | .boolE true => reduceExp env n e2
      | .boolE false => reduceExp env n e3
      | _ => pure (withNote (.ifE e1' e2 e3) e)  -- do not reduce arms

/-- eval.ml:444-446 `reduce_iter`. -/
def reduceIter (env : Env) (fuel : Nat) (it : Iter) : EvalM Iter :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match it with
    | .listN e ido => do pure (.listN (← reduceExp env n e) ido)
    | it => pure it

/-- eval.ml:451-456 `reduce_expfield`. -/
def reduceExpfield (env : Env) (fuel : Nat) (tfs : List TypField)
    (f : ExpField) : EvalM ExpField :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match f with
    | .mk atom e => do
      let e' ← reduceExp env n e
      let (_, _, prems) ← findTypfield tfs atom
      match ← reducePrems env n Subst.empty prems with
      | .no => throw .irred
      | _ => pure (.mk atom e')

/-- eval.ml:458-498 `reduce_path` (continuation-passing, like OCaml). -/
def reducePath (env : Env) (fuel : Nat) (e : Exp) (p : Path)
    (f : Exp → Path → EvalM Exp) : EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match p.it with
    | .rootP => f e p
    | .idxP p1 e1 => do
      let e1' ← reduceExp env n e1
      reducePath env n e p1 (fun e' p1' =>
        match e'.it, e1'.it with
        | .listE es, .numE (.nat i) =>
          if i < es.length then do
            let es' ← es.mapIdxM (fun j eJ =>
              if j == i then f eJ p1' else pure eJ)
            pure (withNote (.listE es') e')
          else f e' (Path.mk (.idxP p1' e1') p.note)
        | _, _ => f e' (Path.mk (.idxP p1' e1') p.note))
    | .sliceP p1 e1 e2 => do
      let e1' ← reduceExp env n e1
      let e2' ← reduceExp env n e2
      reducePath env n e p1 (fun e' p1' =>
        match e'.it, e1'.it, e2'.it with
        | .listE es, .numE (.nat i), .numE (.nat len) =>
          if i + len < es.length then do
            let ea := withNote (.listE (es.take i)) e'
            let eb := withNote (.listE ((es.drop i).take len)) e'
            let ec := withNote (.listE (es.drop (i + len))) e'
            let mid ← f eb p1'
            reduceExp env n
              (withNote (.catE ea (withNote (.catE mid ec) e')) e')
          else f e' (Path.mk (.sliceP p1' e1' e2') p.note)
        | _, _, _ => f e' (Path.mk (.sliceP p1' e1' e2') p.note))
    | .dotP p1 atom => do
      reducePath env n e p1 (fun e' p1' =>
        match e'.it with
        | .strE efs => do
          let tfs ← asStructTyp env n e'.note
          let efs' ← efs.mapM (fun fld => match fld with
            | .mk atomI eI =>
              if eqAtom atomI atom then do
                let eI' ← f eI p1'
                reduceExpfield env n tfs (.mk atomI eI')
              else pure (.mk atomI eI))
          pure (withNote (.strE efs') e')
        | _ => f e' (Path.mk (.dotP p1' atom) p.note))

/-- eval.ml:500-509 `reduce_arg`. -/
def reduceArg (env : Env) (fuel : Nat) (a : Arg) : EvalM Arg :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match a with
    | .expA e => do pure (.expA (← reduceExp env n e))
    | .typA _ => pure a  -- types are reduced on demand
    | .defA _ => pure a
    | .gramA _ => pure a

/-- eval.ml:511-531 `reduce_exp_call` (flag=true: no-clause → none;
Irred match → next clause). -/
def reduceExpCall (env : Env) (fuel : Nat) (x : Id) (args : List Arg) :
    List Clause → EvalM (Option Exp) :=
  fun clauses =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match clauses with
    | [] =>
      pure none
    | .mk _ _ args' body prems :: clauses' =>
      catchIrred
        (do
          match ← matchListM (fun s a1 a2 => matchArg env n s a1 a2)
              Subst.empty args args' with
          | none => reduceExpCall env n x args clauses'
          | some s =>
            match ← reducePrems env n s prems with
            | .unknown =>
              pure none
            | .no => reduceExpCall env n x args clauses'
            | .yes s'' => do
              -- body substituted with arg AND premise bindings (see
              -- reducePrems divergence note)
              pure (some (← reduceExp env n (← liftS (Subst.substExpOpt s'' body)))))
        (fun _ => reduceExpCall env n x args clauses')

/-- eval.ml:533-539 `reduce_prems`. DIVERGENCE (logged, necessity):
upstream returns only `bool option` and reduce_exp_call substitutes the
clause body with the ARGUMENT bindings alone (eval.ml:531) — premise
`let`-bindings never reach the body, which is inadequate for let-premised
clauses (`$instantiate`, allocators…; the middlend never evaluates such
functions, so upstream never hits this — candidate upstream report). We
return the accumulated substitution so callers can substitute bodies
correctly. -/
def reducePrems (env : Env) (fuel : Nat) (s : Subst)
    (prems : List Prem) (deferred : List Prem := [])
    (prog : Bool := false) : EvalM PremRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prems with
    | [] =>
      -- WORKLIST DEFERRAL (mirrors Rel.checkPrems; see its doc): an
      -- undecidable premise still carrying free variables is retried
      -- after later premises extend the substitution ($allocmodule's
      -- forward guess, 4.4-execution.modules.spectec:121-133)
      if deferred.isEmpty then pure (.yes s)
      else if prog then reducePrems env n s deferred [] false
      else pure .unknown
    | prem :: prems' => do
      let premS ← liftS (Subst.substPrem s prem)
      match ← reducePrem env n premS with
      | .yes s' => reducePrems env n (Subst.union s s') prems' deferred true
      | .no => pure .no
      | .unknown =>
        if hasVarPrem premS then
          reducePrems env n s prems' (deferred ++ [prem]) prog
        else pure .unknown

/-- eval.ml:541-671 `reduce_prem`. -/
def reducePrem (env : Env) (fuel : Nat) (prem : Prem) : EvalM PremRes :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prem with
    | .rulePr _ _ _ _ => pure .unknown
    | .ifPr e => do
      match (← reduceExp env n e).it with
      | .boolE b => pure (if b then .yes Subst.empty else .no)
      | _ =>
        -- binding-if equations (`-- if x* = $f(…)`, `-- if type = TYPE
        -- rectype`): the middlend rewrites these to `let` before AL
        -- (il2al); our raw IL keeps them, so an undecidable equality is
        -- executed as a pattern match, either orientation (engine-level
        -- rule, same as Rel.checkPrems; logged)
        match e.it with
        | .cmpE .eq _ a b => do
          -- ground solutions only: bindings still carrying free vars
          -- must wait for the defining premises (worklist deferral)
          let ground := fun (s' : Subst) =>
            s'.varid.entries.all (fun p => !hasVarExp p.2)
          let r1 ← catchIrred
            (matchExp env n Subst.empty a b) (fun _ => pure none)
          match r1 with
          | some s' => if ground s' then pure (.yes s') else pure .unknown
          | none => do
            let r2 ← catchIrred
              (matchExp env n Subst.empty b a) (fun _ => pure none)
            match r2 with
            | some s' => if ground s' then pure (.yes s') else pure .unknown
            | none => pure .unknown
        | _ => pure .unknown
    | .elsePr => pure (.yes Subst.empty)
    | .letPr _ e1 e2 =>
      catchIrred
        (do
          match ← matchExp env n Subst.empty e2 e1 with
          | some s => pure (.yes s)
          | none => pure .unknown)
        (fun _ => pure .unknown)
    | .negPr prem1 => do
      -- eval.ml:556-561 inverts only DECIDED truth. EXTENSION (audit
      -- dim1-2/V9): our ifPr row can return `.yes` from a GUESSED
      -- binding-equation witness (non-empty substitution); existence of
      -- a solving substitution does not decide the equality, so it must
      -- not become definite falsity of the negation.
      match ← reducePrem env n prem1 with
      | .yes s' => if Subst.isEmpty s' then pure .no else pure .unknown
      | .no => pure (.yes Subst.empty)
      | .unknown => pure .unknown
    | .iterPr prem1 (.mk iter xes) => do
      let iter' ← reduceIter env n iter
      let xes' ← xes.mapM (fun d => match d with
        | .mk x ex => do pure (Dom.mk x (← reduceExp env n ex)))
      -- partition out-bound (let-defined) vs in-bound (eval.ml:566-575)
      let flags ← xes'.mapM (fun d => isLetBound env n prem1 d)
      let tagged := xes'.zip flags
      let xesOut := (tagged.filter (·.2)).map (·.1)
      let xesIn := (tagged.filter (!·.2)).map (·.1)
      let xsOut := xesOut.map (fun d => match d with | .mk x _ => x)
      let esOut := xesOut.map (fun d => match d with | .mk _ ex => ex)
      let xsIn := xesIn.map (fun d => match d with | .mk x _ => x)
      let esIn := xesIn.map (fun d => match d with | .mk _ ex => ex)
      let isListN := match iter' with | .listN _ _ => true | _ => false
      if !(esIn.all isHeadNormalExp) || (!isListN && esIn.isEmpty) then
        pure .unknown
      else
        match iter' with
        | .opt => do
          let eosIn ← esIn.mapM asOptExp
          if eosIn.all Option.isNone then pure (.yes Subst.empty)
          else if eosIn.all Option.isSome then do
            let es1In := eosIn.filterMap id
            let s := (xsIn.zip es1In).foldl
              (fun s (x, ex) => Subst.addVarid s x ex) Subst.empty
            match ← reducePrem env n (← liftS (Subst.substPrem s prem1)) with
            | .unknown => pure .unknown
            | .no => pure .no
            | .yes s' => do
              -- reverse-match out-bound values (eval.ml:598-608)
              let r ← (xsOut.zip esOut).foldlM
                (fun (acc : Option Subst) xe => do
                  let (xI, eI) := xe
                  match acc with
                  | none => pure none
                  | some sA => do
                    let tI ← match eI.note with
                      | .iterT tI _ => pure tI
                      | _ => err "IterPr: out-bound variable note not IterT"
                    let inner ← liftS (Subst.substExpOpt s' (Exp.mk (.varE xI) tI))
                    matchExp' env n sA
                      (withNote (.optE (some inner)) eI) eI)
                (some Subst.empty)
              match r with
              | some s'' => pure (.yes s'')
              | none => pure .unknown
          else pure .unknown
        | .list | .list1 => do
          let len ← match esIn with
            | e0 :: _ => do pure (← asListExp e0).length
            | [] => throw (.failure "as_list_exp")
          let isList := match iter' with | .list => true | _ => false
          if isList || len ≥ 1 then
            let en : Exp := .mk (.numE (.nat len)) (.numT .nat)
            reducePrem env n (.iterPr prem1 (.mk (.listN en none) xes'))
          else pure .unknown
        | .listN lenE xo => do
          match lenE.it with
          | .numE (.nat len) => do
            let essIn ← esIn.mapM asListExp
            if !(essIn.all (fun es => es.length == len)) then pure .unknown
            else do
              let rs ← (List.range len).mapM (fun i => do
                let esIIn := essIn.map (fun es => es[i]!)
                let s := (xsIn.zip esIIn).foldl
                  (fun s (x, ex) => Subst.addVarid s x ex) Subst.empty
                let s' := match xo with
                  | none => s
                  | some xc =>
                    Subst.addVarid s xc (.mk (.numE (.nat i)) (.numT .nat))
                reducePrem env n (← liftS (Subst.substPrem s' prem1)))
              if rs.any (fun r => match r with | .unknown => true | _ => false)
              then pure .unknown
              else if rs.any (fun r => match r with | .no => true | _ => false)
              then pure .no
              else do
                let ss := rs.filterMap (fun r => match r with
                  | .yes s => some s | _ => none)
                -- aggregate out-lists (eval.ml:652-661)
                let esOut' ← (xsOut.zip esOut).mapM (fun (xI, eI) => do
                  let tI ← match eI.note with
                    | .iterT tI _ => pure tI
                    | _ => err "IterPr: out-bound variable note not IterT"
                  let esI ← ss.mapM (fun sJ =>
                    liftS (Subst.substExpOpt sJ (Exp.mk (.varE xI) tI)))
                  pure (withNote (.listE esI) eI))
                match ← matchListM (fun s a b => matchExp env n s a b)
                    Subst.empty esOut' esOut with
                | some s' => pure (.yes s')
                | none => pure .unknown
          | _ => pure .unknown

/-- eval.ml:566-574 `is_let_bound`. -/
def isLetBound (env : Env) (fuel : Nat) (prem : Prem) (d : Dom) :
    EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match d with
    | .mk x _ =>
      match prem with
      | .letPr qs _ _ =>
        pure (IdSet.mem x (Free.boundQuants qs).varid)
      | .iterPr premI (.mk iterI xesI) => do
        let _iterI' ← reduceIter env n iterI
        let xesI' ← xesI.mapM (fun d1 => match d1 with
          | .mk x1 ex1 => do pure (Dom.mk x1 (← reduceExp env n ex1)))
        let flags ← xesI'.mapM (fun d1 => isLetBound env n premI d1)
        let outs := (xesI'.zip flags).filter (·.2) |>.map (·.1)
        pure (outs.any (fun d1 => match d1 with
          | .mk _ e1 => IdSet.mem x (Free.freeExp e1).varid))
      | _ => pure false

/-- eval.ml:678-685 `match_iter`. -/
def matchIter (env : Env) (fuel : Nat) (s : Subst) (it1 it2 : Iter) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match it1, it2 with
    | .opt, .opt => pure (some s)
    | .list, .list => pure (some s)
    | .list1, .list1 => pure (some s)
    | .listN e1 _, .listN e2 _ => matchExp env n s e1 e2
    | .opt, .list | .list1, .list | .listN _ _, .list => pure (some s)
    | _, _ => pure none

/-- eval.ml:690-723 `match_typ`. -/
def matchTyp (env : Env) (fuel : Nat) (s : Subst) (t1 t2 : Typ) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match t1, t2 with
    | _, .varT x2 [] =>
      if s.typid.mem x2 then do
        matchTyp env n s t1 (← liftS (Subst.substTypOpt s t2))
      else if !(env.typs.mem x2) then
        -- unbound type = pattern variable
        pure (some (Subst.addTypid s x2 t1))
      else matchTypStep env n s t1 t2
    | _, _ => matchTypStep env n s t1 t2

/-- The non-pattern-variable rows of match_typ (eval.ml:701-723). -/
def matchTypStep (env : Env) (fuel : Nat) (s : Subst) (t1 t2 : Typ) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match t1, t2 with
    | .varT x1 args1, .varT x2 args2 =>
      if x1 == x2 then do
        match ← matchListM (fun s a b => matchArg env n s a b) s args1 args2 with
        | some s' => pure (some s')
        | none => do
          let t1' ← reduceTyp env n t1
          let t2' ← reduceTyp env n t2
          if eqTyp t1 t1' && eqTyp t2 t2' then pure none
          else matchTyp env n s t1' t2'
      else do
        let t1' ← reduceTyp env n t1
        if eqTyp t1 t1' then pure none else matchTyp env n s t1' t2
    | .varT _ _, _ => do
      let t1' ← reduceTyp env n t1
      if eqTyp t1 t1' then pure none else matchTyp env n s t1' t2
    | _, .varT _ _ => do
      let t2' ← reduceTyp env n t2
      if eqTyp t2 t2' then pure none else matchTyp env n s t1 t2'
    | .tupT xts1, .tupT xts2 =>
      matchListM (fun s b1 b2 => matchTypbind env n s b1 b2) s xts1 xts2
    | .iterT t11 it1, .iterT t21 it2 => do
      match ← matchTyp env n s t11 t21 with
      | none => pure none
      | some s' => matchIter env n s' it1 it2
    | _, _ => pure none

/-- eval.ml:725-728 `match_typbind`. -/
def matchTypbind (env : Env) (fuel : Nat) (s : Subst) (b1 b2 : TypBind) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match b1, b2 with
    | .mk x1 t1, .mk x2 t2 => do
      let s' := Subst.addVarid s x2 (Exp.mk (.varE x1) t1)
      matchTyp env n s' t1 (← liftS (Subst.substTypOpt s t2))

/-- eval.ml:733-734 `match_exp`. -/
def matchExp (env : Env) (fuel : Nat) (s : Subst) (e1 e2 : Exp) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    matchExp' env n s (← reduceExp env n e1) e2

/-- eval.ml:736-910 `match_exp'`. OCaml's guarded rows fall through;
mirrored with in-arm conditionals whose fallbacks reproduce the reachable
later rows (`is_head_normal → none`, else `.irred`). -/
def matchExp' (env : Env) (fuel : Nat) (s : Subst) (e1 e2 : Exp) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    -- eval.ml:743 (HACK)
    if eqExp e1 e2 && isNormalExp e1 && isNormalExp e2 then pure (some s)
    else do
    let e2r ← reduceExp env n (← liftS (Subst.substExpOpt s e2))
    let fallThrough : Unit → EvalM (Option Subst) := fun _ =>
      if isHeadNormalExp e1 then pure none else throw .irred
    match e1.it, e2r.it with
    | _, .varE x2 =>
      if s.varid.mem x2 then do
        -- non-linear pattern variable
        if ← equivExp env n e1 (← liftS (Subst.substExpOpt s e2)) then
          pure (some s)
        else pure none
      else do
        -- fresh pattern variable (eval.ml:751-754)
        let e1' ← reduceExp env n (Exp.mk (.subE e1 e1.note e2.note) e2.note)
        pure (some (Subst.addVarid s x2 e1'))
    | .boolE b1, .boolE b2 =>
      if b1 == b2 then pure (some s) else fallThrough ()
    | .numE n1, .numE n2 =>
      if n1 == n2 then pure (some s) else fallThrough ()
    | .textE s1, .textE s2 =>
      if s1 == s2 then pure (some s) else fallThrough ()
    | .numE n1, .unE op _ e21 =>
      -- eval.ml:758-761 (guards fall through to head-normal → none)
      if op == .plus && !(NumOps.isNeg n1) then
        matchExp env n s e1 e21
      else if op == .minus && NumOps.isNeg n1 then do
        matchExp env n s
          (← reduceExp env n (Exp.mk (.numE (NumOps.abs n1)) e1.note)) e21
      else fallThrough ()
    | .numE n1, .cvtE e21 nt1 _ => do
      checkNoReal n1
      if nt1 == .real then
        err "real arithmetic unsupported (fail-closed; zero corpus coverage)"
      match NumOps.cvt nt1 n1 with
      | some n1' => matchExp env n s (withNote (.numE n1') e1) e21
      | none => pure none
    | .listE es1, .listE es2 =>
      matchListM (fun s a b => matchExp' env n s a b) s es1 es2
    | .tupE es1, .tupE es2 =>
      matchListM (fun s a b => matchExp' env n s a b) s es1 es2
    | _, .tupE es2 => do
      match ← etaTupExp env n e1 with
      | none => pure none
      | some es1 => matchListM (fun s a b => matchExp' env n s a b) s es1 es2
    | .listE es1, .catE e21 e22 =>
      -- eval.ml:780-789, both orientations, guards fall through
      (match e21.it with
      | .listE es21 =>
        if es21.length ≤ es1.length then do
          let es11 := es1.take es21.length
          let es12 := es1.drop es21.length
          match ← matchExp' env n s (withNote (.listE es11) e1) e21 with
          | none => pure none
          | some s' => matchExp' env n s' (withNote (.listE es12) e1) e22
        else matchCatRight env n s e1 es1 e21 e22 fallThrough
      | _ => matchCatRight env n s e1 es1 e21 e22 fallThrough)
    | .strE efs1, .strE efs2 =>
      matchListM (fun s f1 f2 => matchExpfield env n s f1 f2) s efs1 efs2
    | .caseE op1 e11, .caseE op2 e21 =>
      if eqMixop op1 op2 then matchExp' env n s e11 e21
      else fallThrough ()
    | _, .uncaseE e21 op =>
      matchExp' env n s (Exp.mk (.caseE op e1) e21.note) e21
    | _, .projE e21 0 =>  -- only valid on unary tuples (eval.ml:819)
      matchExp' env n s (Exp.mk (.tupE [e1]) e21.note) e21
    | .optE none, .iterE _ (.mk .opt xes) =>
      -- eval.ml:830-834
      xes.foldlM
        (fun (acc : Option Subst) d => do
          match acc, d with
          | none, _ => pure none
          | some sA, .mk _ eI => matchExp' env n sA e1 eI)
        (some s)
    | .optE (some e11), .iterE e21 (.mk .opt xes) => do
      -- eval.ml:835-843
      match ← matchExp' env n s e11 e21 with
      | none => pure none
      | some s' => do
        let s0 := xes.foldl (fun s d => match d with
          | .mk x _ => Subst.removeVarid s x) s
        let r ← xes.foldlM
          (fun (acc : Option Subst) d => do
            match acc, d with
            | none, _ => pure none
            | some sAcc, .mk xI exI => do
              let tI ← match exI.note with
                | .iterT tI _ => pure tI
                | _ => err "match: iteration variable note not IterT"
              let inner ← liftS (Subst.substExpOpt s' (Exp.mk (.varE xI) tI))
              matchExp' env n sAcc
                (withNote (.optE (some inner)) e2) exI)
          (some s0)
        match r with
        | none => pure none
        | some s'' => pure (some (Subst.union s'' s))
    | .listE _, .iterE e21 (.mk .list xes) =>
      -- eval.ml:844-846
      let en : Exp := .mk (.varE "_") (.numT .nat)
      matchExp' env n s e1 (withNote (.iterE e21 (.mk (.listN en none) xes)) e2)
    | .listE es1, .iterE e21 (.mk .list1 xes) =>
      -- eval.ml:847-850
      if es1.isEmpty then pure none
      else
        let en : Exp := .mk (.varE "_") (.numT .nat)
        matchExp' env n s e1
          (withNote (.iterE e21 (.mk (.listN en none) xes)) e2)
    | .listE es1, .iterE e21 (.mk (.listN en idOpt) xes) => do
      -- eval.ml:851-875
      let en' : Exp := .mk (.numE (.nat es1.length)) (.numT .nat)
      match ← matchExp' env n s en' en with
      | none => pure none
      | some s' => do
        let s'' := xes.foldl (fun s d => match d with
          | .mk x _ => Subst.removeVarid s x) s'
        let rAcc ← es1.zipIdx.foldlM
          (fun (acc : Option (List Subst)) ej => do
            match acc with
            | none => pure none
            | some accL => do
              let (e1J, j) := ej
              let s''' := match idOpt with
                | none => s''
                | some xJ =>
                  Subst.addVarid s'' xJ (.mk (.numE (.nat j)) (.numT .nat))
              match ← matchExp' env n s''' e1J
                  (← liftS (Subst.substExpOpt s''' e21)) with
              | none => pure none
              | some sJ => pure (some (sJ :: accL)))
          (some [])
        match rAcc.map List.reverse with
        | none => pure none
        | some ss => do
          let rVar ← xes.foldlM
            (fun (acc : Option Subst) d => do
              match acc, d with
              | none, _ => pure none
              | some sAcc, .mk xI exI => do
                let tI ← match exI.note with
                  | .iterT tI _ => pure tI
                  | _ => err "match: iteration variable note not IterT"
                let esI ← ss.mapM (fun sJ =>
                  liftS (Subst.substExpOpt sJ (Exp.mk (.varE xI) tI)))
                matchExp' env n sAcc (withNote (.listE esI) e2) exI)
            (some s')
          match rVar with
          | none => pure none
          | some s''' => pure (some (Subst.union s''' s))
    | _, .iterE e21 it2 => do
      -- eval.ml:876-879 (η-expansion)
      let (e11, it1) ← etaIterExp env n e1
      match ← matchExp' env n s e11 e21 with
      | none => pure none
      | some s' => matchIterexp env n s' it1 it2
    | .subE e11 t11 _, .subE e21 t21 _ => do
      -- eval.ml:880-883, monadic guards with fall-through to the
      -- rhs-SubE handler
      if ← subTyp env n t11 t21 then
        matchExp' env n s
          (← reduceExp env n (withNote (.subE e11 t11 t21) e21)) e21
      else if ← disjTyp env n t11 t21 then pure none
      else matchRhsSubE env n s e1 e2r fallThrough
    | _, .subE _ _ _ => matchRhsSubE env n s e1 e2r fallThrough
    | _, _ => fallThrough ()

/-- eval.ml:780-789 second orientation (rhs `CatE (_, ListE)`). -/
def matchCatRight (env : Env) (fuel : Nat) (s : Subst) (e1 : Exp)
    (es1 : List Exp) (e21 e22 : Exp)
    (fallThrough : Unit → EvalM (Option Subst)) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match e22.it with
    | .listE es22 =>
      if es22.length ≤ es1.length then do
        let k := es1.length - es22.length
        let es11 := es1.take k
        let es12 := es1.drop k
        match ← matchExp' env n s (withNote (.listE es11) e1) e21 with
        | none => pure none
        | some s' => matchExp' env n s' (withNote (.listE es12) e1) e22
      else fallThrough ()
    | _ => fallThrough ()

/-- eval.ml:884-907 the rhs-SubE rows. -/
def matchRhsSubE (env : Env) (fuel : Nat) (s : Subst) (e1 e2r : Exp)
    (fallThrough : Unit → EvalM (Option Subst)) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match e2r.it with
    | .subE e21 t21 _ => do
      if ← subTyp env n e1.note t21 then
        matchExp' env n s
          (← reduceExp env n (withNote (.subE e1 e1.note t21) e21)) e21
      else if isHeadNormalExp e1 then do
        let t21' ← reduceTyp env n t21
        let ok ← (match e1.it, t21' with
          | .boolE _, .boolT => pure true
          | .numE _, .numT _ => pure true
          | .textE _, .textT => pure true
          | .caseE op _, .varT _ _ => do
            match ← reduceTypdef env n t21 with
            | .variantT tcs =>
              -- assumes shallow subtyping (eval.ml:897)
              pure (tcs.any (fun c => match c with
                | .mk opN _ _ _ => eqMixop opN op))
            | _ => pure false
          | .varE x1, _ => do
            let t1 ← match env.findVar? x1 with
              | some t => pure t
              | none => err s!"undeclared variable `{x1}`"
            if ← subTyp env n (← reduceTyp env n t1) t21 then pure true
            else throw .irred
          | _, _ => pure false)
        if ok then matchExp' env n s (Exp.mk e1.it t21) e21
        else pure none
      else throw .irred
    | _ => fallThrough ()

/-- eval.ml:912-914 `match_expfield`. -/
def matchExpfield (env : Env) (fuel : Nat) (s : Subst) (f1 f2 : ExpField) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match f1, f2 with
    | .mk a1 e1, .mk a2 e2 => do
      if !eqAtom a1 a2 then pure none
      else matchExp' env n s e1 (← liftS (Subst.substExpOpt s e2))

/-- eval.ml:916-917 `match_iterexp`. -/
def matchIterexp (env : Env) (fuel : Nat) (s : Subst)
    (it1 it2 : IterExp) : EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match it1, it2 with
    | .mk i1 _, .mk i2 _ => matchIter env n s i1 i2

/-- eval.ml:920-933 `eta_tup_exp`. -/
def etaTupExp (env : Env) (fuel : Nat) (e : Exp) :
    EvalM (Option (List Exp)) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let xts ← match ← reduceTyp env n e.note with
      | .tupT xts => pure xts
      | _ => err "eta_tup_exp: type not a tuple"
    let (accRev, _, _) ← xts.foldlM
      (fun (st : List Exp × Nat × Subst) b => do
        let (acc, i, sA) := st
        match b with
        | .mk xI tI => do
          let eI' := Exp.mk (.projE e i) (← liftS (Subst.substTypOpt sA tI))
          pure (eI' :: acc, i + 1, Subst.addVarid sA xI eI'))
      (([] : List Exp), 0, Subst.empty)
    pure (some accRev.reverse)

/-- eval.ml:935-943 `eta_iter_exp`. -/
def etaIterExp (env : Env) (fuel : Nat) (e : Exp) :
    EvalM (Exp × IterExp) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match ← reduceTyp env n e.note with
    | .iterT t .opt => do
      pure (← reduceExp env n (Exp.mk (.theE e) t), .mk .opt [])
    | .iterT t .list => do
      let len ← reduceExp env n (Exp.mk (.lenE e) (.numT .nat))
      pure (Exp.mk (.idxE e (.mk (.varE "_i_") (.numT .nat))) t,
            .mk (.listN len (some "_i_")) [])
    -- eval.ml:943 `assert false` (unreachable under upstream's oriented
    -- `let`-matching); our both-orientation binding-eq attempts CAN land
    -- here with a mismatched pair — throw `.irred` so the enclosing
    -- catchIrred falls through to the other orientation (engine-level)
    | _ => throw .irred

/-- eval.ml:948-960 `match_sym`. -/
def matchSym (env : Env) (fuel : Nat) (s : Subst) (g1 g2 : Sym) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match g1, g2 with
    | _, .varG x2 [] =>
      if s.gramid.mem x2 then do
        matchSym env n s g1 (← liftS (Subst.substSymOpt s g2))
      else if !(env.grams.mem x2) then
        pure (some (Subst.addGramid s x2 g1))
      else matchSymStep env n s g1 g2
    | _, _ => matchSymStep env n s g1 g2

def matchSymStep (env : Env) (fuel : Nat) (s : Subst) (g1 g2 : Sym) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match g1, g2 with
    | .varG x1 args1, .varG x2 args2 =>
      if x1 == x2 then
        matchListM (fun s a b => matchArg env n s a b) s args1 args2
      else pure none
    | .iterG g11 it1, .iterG g21 it2 => do
      match ← matchSym env n s g11 g21 with
      | none => pure none
      | some s' => matchIterexp env n s' it1 it2
    | _, _ => pure none

/-- eval.ml:965-972 `match_arg` (sort mismatch is an assert upstream;
fail closed). -/
def matchArg (env : Env) (fuel : Nat) (s : Subst) (a1 a2 : Arg) :
    EvalM (Option Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match a1, a2 with
    | .expA e1, .expA e2 => matchExp env n s e1 e2
    | .typA t1, .typA t2 => matchTyp env n s t1 t2
    | .defA x1, .defA x2 => pure (some (Subst.addDefid s x1 x2))
    | .gramA g1, .gramA g2 => matchSym env n s g1 g2
    | _, _ => err "match_arg: sort mismatch (assert upstream, eval.ml:972)"

/-- eval.ml:977-998 `equiv_typ`. -/
def equivTyp (env : Env) (fuel : Nat) (t1 t2 : Typ) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match t1, t2 with
    | .varT x1 as1, .varT x2 as2 => do
      -- CAUTION: `if A && (← m)` hoists m unconditionally in Lean do-
      -- notation; OCaml && short-circuits (eval.ml:983,986). Sequenced
      -- explicitly.
      let quick ← if x1 == x2 then
          equivListM (fun a b => equivArg env n a b) as1 as2
        else pure false
      if quick then pure true
      else do
        let t1' ← reduceTyp env n t1
        let t2' ← reduceTyp env n t2
        let progressed := !eqTyp t1 t1' || !eqTyp t2 t2'
        let viaReduce ← if progressed then equivTyp env n t1' t2'
          else pure false
        if viaReduce then pure true
        else do
          pure (eqDeftyp (← reduceTypdef env n t1') (← reduceTypdef env n t2'))
    | .varT _ _, _ => do
      let t1' ← reduceTyp env n t1
      if eqTyp t1 t1' then pure false else equivTyp env n t1' t2
    | _, .varT _ _ => do
      let t2' ← reduceTyp env n t2
      if eqTyp t2 t2' then pure false else equivTyp env n t1 t2'
    | .tupT xts1, .tupT xts2 => equivTup env n Subst.empty xts1 xts2
    | .iterT t11 it1, .iterT t21 it2 => do
      if ← equivTyp env n t11 t21 then equivIter env n it1 it2
      else pure false
    | _, _ => pure (eqTyp t1 t2)

/-- eval.ml:1000-1005 `equiv_tup`. -/
def equivTup (env : Env) (fuel : Nat) (s : Subst) :
    List TypBind → List TypBind → EvalM Bool :=
  fun xts1 xts2 =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match xts1, xts2 with
    | .mk x1 t1 :: r1, .mk x2 t2 :: r2 => do
      if ← equivTyp env n t1 (← liftS (Subst.substTypOpt s t2)) then
        equivTup env n (Subst.addVarid s x2 (Exp.mk (.varE x1) t1)) r1 r2
      else pure false
    | [], [] => pure true
    | _, _ => pure false

/-- eval.ml:1007-1011 `equiv_iter`. -/
def equivIter (env : Env) (fuel : Nat) (it1 it2 : Iter) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match it1, it2 with
    | .listN e1 ido1, .listN e2 ido2 => do
      if ← equivExp env n e1 e2 then pure (ido1 == ido2) else pure false
    | .opt, .opt | .list, .list | .list1, .list1 => pure true
    | _, _ => pure false

/-- eval.ml:1026-1031 `equiv_exp`. -/
def equivExp (env : Env) (fuel : Nat) (e1 e2 : Exp) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    pure (eqExp (← reduceExp env n e1) (← reduceExp env n e2))

/-- eval.ml:1033-1037 `equiv_sym`. -/
def equivSym (_env : Env) (fuel : Nat) (g1 g2 : Sym) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | _+1 => pure (eqSym g1 g2)

/-- eval.ml:1039-1048 `equiv_arg`. -/
def equivArg (env : Env) (fuel : Nat) (a1 a2 : Arg) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match a1, a2 with
    | .expA e1, .expA e2 => equivExp env n e1 e2
    | .typA t1, .typA t2 => equivTyp env n t1 t2
    | .defA x1, .defA x2 => pure (x1 == x2)
    | .gramA g1, .gramA g2 => equivSym env n g1 g2
    | _, _ => pure false

/-- eval.ml:1051-1055 `equiv_functyp`. -/
def equivFunctyp (env : Env) (fuel : Nat)
    (f1 f2 : List Param × Typ) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let (ps1, t1) := f1
    let (ps2, t2) := f2
    if ps1.length != ps2.length then pure false
    else
      match ← equivParams env n Subst.empty ps1 ps2 with
      | none => pure false
      | some s => do equivTyp env n t1 (← liftS (Subst.substTypOpt s t2))

/-- eval.ml:1057-1072 `equiv_params` (sort mismatch: assert upstream). -/
def equivParams (env : Env) (fuel : Nat) (s : Subst) :
    List Param → List Param → EvalM (Option Subst) :=
  fun ps1 ps2 =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match ps1, ps2 with
    | [], [] => pure (some s)
    | p1 :: r1, p2 :: r2 => do
      let p2' ← liftS (Subst.substParam s p2)
      match p1, p2' with
      | .expP x1 t1, .expP x2 t2 => do
        if !(← equivTyp env n t1 t2) then pure none
        else
          equivParams env n
            (Subst.addVarid s x2 (Exp.mk (.varE x1) t1)) r1 r2
      | .typP _, .typP _ => equivParams env n s r1 r2
      | .defP x1 ps1' t1, .defP x2 ps2' t2 => do
        if !(← equivFunctyp env n (ps1', t1) (ps2', t2)) then pure none
        else equivParams env n (Subst.addDefid s x2 x1) r1 r2
      | .gramP x1 ps1' t1, .gramP x2 ps2' t2 => do
        if !(← equivFunctyp env n (ps1', t1) (ps2', t2)) then pure none
        else
          equivParams env n (Subst.addGramid s x2 (.varG x1 [])) r1 r2
      | _, _ => err "equiv_params: sort mismatch (assert upstream, eval.ml:1071)"
    | _, _ => pure none

/-- eval.ml:1077-1080 `sub_prems`. -/
def subPrems (_env : Env) (fuel : Nat)
    (prems1 prems2 : List Prem) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | _+1 =>
    pure (prems2.isEmpty ||
      (prems1.length == prems2.length && eqPrems prems1 prems2))

/-- eval.ml:1082 `sub_typ`. -/
def subTyp (env : Env) (fuel : Nat) (t1 t2 : Typ) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => subTyp' env n [] t1 t2

/-- eval.ml:1084-1117 `sub_typ'`. -/
def subTyp' (env : Env) (fuel : Nat) (assum : List (Typ × Typ))
    (t1 t2 : Typ) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    if ← equivTyp env n t1 t2 then pure true
    else if assum.any (fun (a, b) => eqTyp t1 a && eqTyp t2 b) then
      pure true
    else do
      let t1' ← reduceTyp env n t1
      let t2' ← reduceTyp env n t2
      let assum' := (t1, t2) :: assum
      match t1', t2' with
      | .tupT xts1, .tupT xts2 =>
        subTup env n assum' Subst.empty xts1 xts2
      | .varT _ _, .varT _ _ => do
        match ← reduceTypdef env n t1', ← reduceTypdef env n t2' with
        | .structT tfs1, .structT tfs2 =>
          tfs2.allM (fun f2 => match f2 with
            | .mk atom (t21) _ prems2 =>
              match findFieldOpt tfs1 atom with
              | some (t11, _, prems1) => do
                if ← subTyp' env n assum' t11 t21 then
                  subPrems env n prems1 prems2
                else pure false
              | none => pure false)
        | .variantT tcs1, .variantT tcs2 =>
          tcs1.allM (fun c1 => match c1 with
            | .mk mixop t11 _ prems1 =>
              match findCaseOpt tcs2 mixop with
              | some (t21, _, prems2) => do
                if ← subTyp' env n assum' t11 t21 then
                  subPrems env n prems1 prems2
                else pure false
              | none => pure false)
        | _, _ => pure false
      | .iterT t11 it1, .iterT t21 it2 => do
        if ← subTyp' env n assum' t11 t21 then pure (eqIter it1 it2)
        else pure false
      | _, _ => pure false

/-- eval.ml:1119-1124 `sub_tup`. -/
def subTup (env : Env) (fuel : Nat) (assum : List (Typ × Typ))
    (s : Subst) : List TypBind → List TypBind → EvalM Bool :=
  fun xts1 xts2 =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match xts1, xts2 with
    | .mk x1 t1 :: r1, .mk x2 t2 :: r2 => do
      if ← subTyp' env n assum t1 (← liftS (Subst.substTypOpt s t2)) then
        subTup env n assum
          (Subst.addVarid s x2 (Exp.mk (.varE x1) t1)) r1 r2
      else pure false
    | [], [] => pure true
    | _, _ => pure false

/-- eval.ml:1136-1169 `disj_typ`. -/
def disjTyp (env : Env) (fuel : Nat) (t1 t2 : Typ) : EvalM Bool :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match t1, t2 with
    | .varT _ _, .varT _ _ => do
      match ← reduceTypdef env n t1, ← reduceTypdef env n t2 with
      | .structT tfs1, .structT tfs2 =>
        if unordered (atomsSet tfs1) (atomsSet tfs2) then pure true
        else
          tfs2.anyM (fun f2 => match f2 with
            | .mk atom t2f _ _ =>
              match findFieldOpt tfs1 atom with
              | some (t1f, _, _) => disjTyp env n t1f t2f
              | none => pure true)
      | .variantT tcs1, .variantT tcs2 =>
        if IdSet.disjoint (mixopsSet tcs1) (mixopsSet tcs2) then pure true
        else
          tcs1.anyM (fun c1 => match c1 with
            | .mk op t1c _ _ =>
              match findCaseOpt tcs2 op with
              | some (t2c, _, _) => disjTyp env n t1c t2c
              | none => pure false)
      | _, _ => pure true
    | .varT _ _, _ => do
      let t1' ← reduceTyp env n t1
      if eqTyp t1 t1' then pure false else disjTyp env n t1' t2
    | _, .varT _ _ => do
      let t2' ← reduceTyp env n t2
      if eqTyp t2 t2' then pure false else disjTyp env n t1 t2'
    | .tupT xts1, .tupT xts2 => disjTup env n Subst.empty xts1 xts2
    | .iterT t11 it1, .iterT t21 it2 => do
      if ← disjTyp env n t11 t21 then pure true
      else pure (!eqIter it1 it2)
    | _, _ => pure (!(eqTyp t1 t2))

/-- eval.ml:1174-1179 `disj_tup`. -/
def disjTup (env : Env) (fuel : Nat) (s : Subst) :
    List TypBind → List TypBind → EvalM Bool :=
  fun xts1 xts2 =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match xts1, xts2 with
    | .mk x1 t1 :: r1, .mk x2 t2 :: r2 => do
      if ← disjTyp env n t1 (← liftS (Subst.substTypOpt s t2)) then pure true
      else
        disjTup env n (Subst.addVarid s x2 (Exp.mk (.varE x1) t1)) r1 r2
    | [], [] => pure false
    | _, _ => pure true

end

end Eval

end SpecTecLean.Il
