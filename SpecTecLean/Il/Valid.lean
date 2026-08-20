import SpecTecLean.Il.Eval
/-!
IL validation, mirroring `deps/spectec/spectec/src/il/valid.ml` (spectec @
acc6e834 + vendored patch).

Deliberate divergences (logged, arc-2):
- **`valid_atom` is a no-op.** valid.ml:148-150 checks the atom's mutable
  latex `info` (`note.def <> ""`), which the dump deliberately does not
  carry (presentation metadata; `Atom.eq` ignores it, atom.ml:79-80). The
  check guards latex macro generation, not semantics.
- Error messages are structurally faithful but not byte-identical to
  valid.ml's (positions are definition-granular; pretty-printers differ).
  Error TEXT is never compared differentially; dup-detection and
  disjointness KEYS use the exact `Mixop.to_string` mirror (XlOps).
- valid.ml:384's `try infer_exp … with _` catches every exception; we
  catch `.error/.irred/.failure` but PROPAGATE `.fuel` (fuel is our
  scaffolding; masking exhaustion would fake an answer).
- Fuel threading as in Il/Eval.lean.
-/

namespace SpecTecLean.Il

namespace Valid

open Eval

/-- valid.ml:39 `direction` (for error phrasing only). -/
inductive Direction | infer | check

/-- valid.ml:181 `side` (`Lhs/`Rhs). -/
inductive Side where
  | lhs | rhs
deriving BEq

/-- Catch-all mirror of `with _ ->` (valid.ml:384), fuel excepted. -/
def catchAllButFuel (m : EvalM α) (h : Unit → EvalM α) : EvalM α :=
  fun st =>
    match m st with
    | .error .fuel => .error .fuel
    | .error _ => h () st
    | r => r

/-- valid.ml:15-18 `find_field`. -/
def findField (tfs : List TypField) (atom : Atom) :
    EvalM (Typ × List Param × List Prem) :=
  match findFieldOpt tfs atom with
  | some r => pure r
  | none => err s!"unbound field {XlPrint.atomToString atom}"

/-- valid.ml:20-23 `find_case`. -/
def findCase (tcs : List TypCase) (op : Mixop) :
    EvalM (Typ × List Param × List Prem) :=
  match findCaseOpt tcs op with
  | some r => pure r
  | none => err s!"unknown case {XlPrint.mixopToString op}"

/-- valid.ml:36-37 type accessors. -/
def expandTyp (env : Env) (fuel : Nat) (t : Typ) : EvalM Typ :=
  reduceTyp env fuel t

def expandTypdef (env : Env) (fuel : Nat) (t : Typ) : EvalM DefTyp :=
  reduceTypdef env fuel t

/-- valid.ml:54-57 `as_iter_typ`. -/
def asIterTyp (it : Iter) (phrase : String) (env : Env) (fuel : Nat)
    (t : Typ) : EvalM Typ := do
  match ← expandTyp env fuel t with
  | .iterT t1 iter2 =>
    if eqIter it iter2 then pure t1
    else err s!"{phrase}'s type does not match expected iteration type"
  | _ => err s!"{phrase}'s type does not match expected iteration type"

/-- valid.ml:59-62 `as_list_typ`. -/
def asListTyp (phrase : String) (env : Env) (fuel : Nat) (t : Typ) :
    EvalM Typ := do
  match ← expandTyp env fuel t with
  | .iterT t1 .list | .iterT t1 .list1 | .iterT t1 (.listN _ _) => pure t1
  | _ => err s!"{phrase}'s type does not match expected type (_)*"

/-- valid.ml:64-67 `as_tup_typ`. -/
def asTupTyp (phrase : String) (env : Env) (fuel : Nat) (t : Typ) :
    EvalM (List TypBind) := do
  match ← expandTyp env fuel t with
  | .tupT xts => pure xts
  | _ => err s!"{phrase}'s type does not match expected type (_,...,_)"

/-- valid.ml:70-73 `as_struct_typ`. -/
def asStructTypV (phrase : String) (env : Env) (fuel : Nat) (t : Typ) :
    EvalM (List TypField) := do
  match ← expandTypdef env fuel t with
  | .structT tfs => pure tfs
  | _ => err s!"{phrase}'s type does not match expected type (record)"

/-- valid.ml:75-78 `as_variant_typ`. -/
def asVariantTypV (phrase : String) (env : Env) (fuel : Nat) (t : Typ) :
    EvalM (List TypCase) := do
  match ← expandTypdef env fuel t with
  | .variantT tcs => pure tcs
  | _ => err s!"{phrase}'s type does not match expected type | ..."

/-- valid.ml:80-86 `as_comp_typ` (fueled recursion through fields). -/
def asCompTyp (phrase : String) (env : Env) (fuel : Nat) (t : Typ) :
    EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match ← expandTypdef env n t with
    | .aliasT (.iterT _ _) => pure ()
    | .structT tfs =>
      tfs.forM (fun f => match f with
        | .mk _ tf _ _ => asCompTyp phrase env n tf)
    | _ => err s!"{phrase}'s type is not composable"

/-- valid.ml:88-96 `proj_tup_typ`. -/
def projTupTyp (fuel : Nat) (i : Nat) (xts : List TypBind) (e : Exp) :
    EvalM Typ := do
  let rec loop (i : Nat) (xts : List TypBind) (s : Subst) : EvalM Typ :=
    match i, xts with
    | _, [] => err "invalid tuple projection"
    | 0, .mk _ tI :: _ => liftS (Subst.substTypOpt s tI)
    | i+1, .mk xI tI :: xts' => do
      let tI' ← liftS (Subst.substTypOpt s tI)
      let eI : Exp := .mk (.projE e (i+1)) tI'
      -- valid.ml:93-95 binds each earlier component to `ProjE (e, i)`
      -- with the CURRENT countdown value of i — looks like an upstream
      -- index bug, mirrored verbatim (candidate upstream report)
      loop i xts' (Subst.addVarid s xI eI)
  match fuel with
  | 0 => throw .fuel
  | _+1 => loop i xts Subst.empty

/-- valid.ml:101-109 equivalence/subtyping as checks. -/
def equivTypV (env : Env) (fuel : Nat) (t1 t2 : Typ) : EvalM Unit := do
  if ← equivTyp env fuel t1 t2 then pure ()
  else err "expression's type does not equal expected type"

def subTypV (env : Env) (fuel : Nat) (t1 t2 : Typ) : EvalM Unit := do
  if ← subTyp env fuel t1 t2 then pure ()
  else err "expression's type does not match expected supertype"

/-- valid.ml:114-122 `infer_unop`: (operand typ, result typ). -/
def inferUnop (op : UnOp) (ot : OpTyp) : EvalM (Typ × Typ) :=
  match op, ot with
  | .not, .bool => pure (.boolT, .boolT)
  | .plus, .num nt | .minus, .num nt =>
    if NumOps.typUnop op nt nt then pure (.numT nt, .numT nt)
    else err "illegal type for unary operator"
  | _, _ => err "malformed unary operator annotation"

/-- valid.ml:124-137 `infer_binop`: (t1, t2, result). -/
def inferBinop (op : BinOp) (ot : OpTyp) : EvalM (Typ × Typ × Typ) :=
  match op, ot with
  | .and, .bool | .or, .bool | .impl, .bool | .equiv, .bool =>
    pure (.boolT, .boolT, .boolT)
  | .add, .num nt | .sub, .num nt | .mul, .num nt | .div, .num nt
  | .mod, .num nt =>
    if NumOps.typBinop op nt nt nt then pure (.numT nt, .numT nt, .numT nt)
    else err "illegal type for binary operator"
  | .pow, .num nt =>
    let nt2 : NumTyp := if nt == .nat then .nat else .int
    if NumOps.typBinop op nt nt2 nt then
      pure (.numT nt, .numT nt2, .numT nt)
    else err "illegal type for binary operator"
  | _, _ => err "malformed binary operator annotation"

/-- valid.ml:139-143 `infer_cmpop`. -/
def inferCmpop (op : CmpOp) (ot : OpTyp) : EvalM (Option Typ) :=
  match op, ot with
  | .eq, .bool | .ne, .bool => pure none
  | .lt, .num nt | .gt, .num nt | .le, .num nt | .ge, .num nt =>
    pure (some (.numT nt))
  | _, _ => err "malformed comparison operator annotation"

/-- valid.ml:148-153 `valid_atom`/`valid_mixop`: no-ops here (atom latex
info is not dumped; see header). -/
def validAtom (_env : Env) (_a : Atom) : EvalM Unit := pure ()
def validMixop (_env : Env) (_op : Mixop) : EvalM Unit := pure ()

/-- valid.ml:156-165 `check_mixops` (dup detection keyed on the
`Mixop.to_string` mirror — semantic, see XlOps header). -/
def checkMixops (phrase item : String) (list : List Mixop) : EvalM Unit := do
  let keys := list.map XlPrint.mixopToString
  let dups := keys.filter (fun k => (keys.filter (· == k)).length > 1)
  if dups.isEmpty then pure ()
  else err s!"{phrase} contains duplicate {item}(s)"

/-- mixop.ml:44 `arity` (count of Args). -/
def mixopArity (m : Mixop) : Nat :=
  match m with
  | .arg => 1
  | .atom _ => 0
  | .brack _ m1 _ => mixopArity m1
  | .infix m1 _ m2 => mixopArity m1 + mixopArity m2
  | .seq ms => (ms.attach.map (fun ⟨m1, _⟩ => mixopArity m1)).foldl (·+·) 0

mutual

/-- valid.ml:181-188 `valid_iter` (returns the extended env). -/
def validIter (side : Side) (env : Env) (fuel : Nat) (it : Iter) :
    EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match it with
    | .opt | .list | .list1 => pure env
    | .listN e idOpt => do
      validExp side env n e (.numT .nat)
      match idOpt with
      | none => pure env
      | some x => pure (env.bindVar x (.numT .nat))

/-- valid.ml:190-204 `valid_iterexp` (returns iter' and env'). -/
def validIterexp (side : Side) (env : Env) (fuel : Nat) (ie : IterExp) :
    EvalM (Iter × Env) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match ie with
    | .mk it xes => do
      let env' ← validIter side env n it
      let isListN := match it with | .listN _ _ => true | _ => false
      if xes.isEmpty && !isListN && side == .rhs then
        err "vacuous iteration"
      else do
        let it' := match it with | .opt => Iter.opt | _ => Iter.list
        let envOut ← xes.foldlM
          (fun envAcc d => do
            match d with
            | .mk x e => do
              let t ← inferExp env n e
              validExp side env n e t
              let t1 ← asIterTyp it' "iterator" env n t
              pure (envAcc.bindVar x t1))
          env'
        pure (it', envOut)

/-- valid.ml:209 `valid_typ`. -/
def validTyp (env : Env) (fuel : Nat) (t : Typ) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let _ ← validTypBind env n t
    pure ()

/-- valid.ml:211-235 `valid_typ_bind`. -/
def validTypBind (env : Env) (fuel : Nat) (t : Typ) : EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match t with
    | .varT x args => do
      let (ps, _) ← match env.findTyp? x with
        | some d => pure d
        | none => err s!"undeclared type {x}"
      let _ ← validArgs env n args ps Subst.empty
      pure env
    | .boolT | .numT _ | .textT => pure env
    | .tupT [] => pure env
    | .tupT (.mk x1 t1 :: xts) => do
      validTyp env n t1
      validTypBind (env.bindVar x1 t1) n (.tupT xts)
    | .iterT t1 it =>
      match it with
      | .listN _ _ => err "definite iterator not allowed in type"
      | _ => do
        let env' ← validIter .rhs env n it
        validTyp env' n t1
        pure env

/-- valid.ml:237-246 `valid_deftyp`. -/
def validDeftyp (env : Env) (fuel : Nat) (dt : DefTyp) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match dt with
    | .aliasT t => validTyp env n t
    | .structT tfs => do
      checkMixops "record" "field"
        (tfs.map (fun f => match f with | .mk a _ _ _ => .atom a))
      tfs.forM (validTypfield env n)
    | .variantT tcs => do
      checkMixops "variant" "case"
        (tcs.map (fun c => match c with | .mk op _ _ _ => op))
      tcs.forM (validTypcase env n)

/-- valid.ml:248-252 `valid_typfield`. -/
def validTypfield (env : Env) (fuel : Nat) (f : TypField) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match f with
    | .mk atom t qs prems => do
      validAtom env atom
      let env' ← validTypBind env n t
      let env'' ← validQuants env' n qs
      let _ ← validPrems env'' n prems
      pure ()

/-- valid.ml:254-270 `valid_typcase` (incl. the mixop arity check). -/
def validTypcase (env : Env) (fuel : Nat) (c : TypCase) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match c with
    | .mk mixop t qs prems => do
      let arity := match t with
        | .tupT ts => ts.length
        | _ => 1
      if mixopArity mixop != arity then
        err s!"inconsistent arity in mixin notation {XlPrint.mixopToString mixop}"
      else do
        validMixop env mixop
        let env' ← validTypBind env n t
        let env'' ← validQuants env' n qs
        let _ ← validPrems env'' n prems
        pure ()

/-- valid.ml:275-348 `infer_exp`. -/
def inferExp (env : Env) (fuel : Nat) (e : Exp) : EvalM Typ :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match e.it with
    | .varE x =>
      match env.findVar? x with
      | some t => pure t
      | none => err s!"undeclared variable {x}"
    | .boolE _ => pure .boolT
    | .numE v => pure (.numT (NumOps.toTyp v))
    | .textE _ => pure .textT
    | .unE op ot _ => do pure (← inferUnop op ot).2
    | .binE op ot _ _ => do pure (← inferBinop op ot).2.2
    | .cmpE _ _ _ _ | .memE _ _ => pure .boolT
    | .idxE e1 _ => do
      asListTyp "expression" env n (← inferExp env n e1)
    | .sliceE e1 _ _ | .updE e1 _ _ | .extE e1 _ _ | .compE e1 _ =>
      inferExp env n e1
    | .strE _ => err "cannot infer type of record"
    | .dotE e1 atom => do
      let tfs ← asStructTypV "expression" env n (← inferExp env n e1)
      pure (← findField tfs atom).1
    | .tupE es => do
      let binds ← es.mapM (fun eI => do
        pure (TypBind.mk "_" (← inferExp env n eI)))
      pure (.tupT binds)
    | .callE x args => do
      let (ps, t, _) ← match env.findDef? x with
        | some d => pure d
        | none => err s!"undeclared definition {x}"
      let s ← validArgs env n args ps Subst.empty
      liftS (Subst.substTypOpt s t)
    | .iterE e1 ie => do
      let (it, env') ← validIterexp .rhs env n ie
      pure (.iterT (← inferExp env' n e1) it)
    | .projE e1 i => do
      let t1 ← inferExp env n e1
      let xts ← asTupTyp "expression" env n t1
      projTupTyp n i xts e1
    | .uncaseE e1 op => do
      let t1 ← inferExp env n e1
      match ← asVariantTypV "expression" env n t1 with
      | [.mk op' t _ _] =>
        if eqMixop op op' then pure t else err "invalid case projection"
      | _ => err "invalid case projection"
    | .optE _ => err "cannot infer type of option"
    | .theE e1 => do
      asIterTyp .opt "option" env n (← inferExp env n e1)
    | .listE es => do
      match ← es.mapM (inferExp env n) with
      | [] => err "cannot infer type of list"
      | t :: ts =>
        if ts.all (eqTyp t) then pure (.iterT t .list)
        else err "cannot infer type of list"
    | .liftE e1 => do
      let t1 ← asIterTyp .opt "lifting" env n (← inferExp env n e1)
      pure (.iterT t1 .list)
    | .lenE _ => pure (.numT .nat)
    | .catE e1 e2 => do
      let t1 ← inferExp env n e1
      let t2 ← inferExp env n e2
      if eqTyp t1 t2 then pure t1
      else err "cannot infer type of concatenation"
    | .caseE _ _ => pure e.note  -- valid.ml:339
    | .cvtE _ _ t2 => pure (.numT t2)
    | .subE _ _ t2 => pure t2
    | .ifE _ e2 e3 => do
      let t2 ← inferExp env n e2
      let t3 ← inferExp env n e3
      if eqTyp t2 t3 then pure t2
      else err "cannot infer type of if expression: branches differ"

/-- valid.ml:351-509 `valid_exp`. -/
def validExp (side : Side) (env : Env) (fuel : Nat) (e : Exp) (t : Typ) :
    EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    validTyp env n t
    match e.it with
    | .varE x =>
      if x == "_" && side == .lhs then pure ()
      else do
        let t' ← match env.findVar? x with
          | some t' => pure t'
          | none => err s!"undeclared variable {x}"
        equivTypV env n t' t
    | .boolE _ | .numE _ | .textE _ => do
      equivTypV env n (← inferExp env n e) t
    | .unE op nt e1 => do
      let (t1, t') ← inferUnop op nt
      validExp side env n e1 t1
      equivTypV env n t' t
    | .binE op nt e1 e2 => do
      -- valid.ml:369-379: Lhs special-case when one operand is a nat
      -- literal and op is add/sub; guards fall through to the plain row
      let isNatLit := fun (ex : Exp) => match ex.it with
        | .numE (.nat _) => true | _ => false
      let (t1, t2, t') ← inferBinop op nt
      if side == .lhs && (op == .add || op == .sub)
          && (isNatLit e1 || isNatLit e2) then do
        validExp side env n e1 t1
        validExp side env n e2 t2
        equivTypV env n t' t
      else do
        validExp .rhs env n e1 t1
        validExp .rhs env n e2 t2
        equivTypV env n t' t
    | .cmpE op nt e1 e2 => do
      let t' ← match ← inferCmpop op nt with
        | some t' => pure t'
        | none =>
          catchAllButFuel (inferExp env n e1) (fun _ => inferExp env n e2)
      let side' : Side := if op == .eq then .lhs else .rhs  -- HACK (386)
      validExp side' env n e1 t'
      validExp side' env n e2 t'
      equivTypV env n .boolT t
    | .idxE e1 e2 => do
      let t1 ← inferExp env n e1
      let t' ← asListTyp "expression" env n t1
      validExp .rhs env n e1 t1
      validExp .rhs env n e2 (.numT .nat)
      equivTypV env n t' t
    | .sliceE e1 e2 e3 => do
      let _ ← asListTyp "expression" env n t
      validExp .rhs env n e1 t
      validExp .rhs env n e2 (.numT .nat)
      validExp .rhs env n e3 (.numT .nat)
    | .updE e1 p e2 => do
      validExp .rhs env n e1 t
      let t2 ← validPath env n p t
      validExp .rhs env n e2 t2
    | .extE e1 p e2 => do
      validExp .rhs env n e1 t
      let t2 ← validPath env n p t
      let _ ← asListTyp "path" env n t2
      validExp .rhs env n e2 t2
    | .strE efs => do
      let tfs ← asStructTypV "record" env n t
      if efs.length != tfs.length then
        err s!"arity mismatch for expression list, expected {tfs.length}, got {efs.length}"
      else
        (efs.zip tfs).forM (fun (ef, tf) => validExpfield side env n ef tf)
    | .dotE e1 atom => do
      let t1 ← inferExp env n e1
      validExp .rhs env n e1 t1
      validAtom env atom
      let tfs ← asStructTypV "expression" env n t1
      let (t', _, _) ← findField tfs atom
      equivTypV env n t' t
    | .compE e1 e2 => do
      asCompTyp "expression" env n t
      validExp .rhs env n e1 t
      validExp .rhs env n e2 t
    | .memE e1 e2 => do
      let t2 ← inferExp env n e2
      let t1 ← asListTyp "expression" env n t2
      validExp .rhs env n e1 t1
      validExp .rhs env n e2 t2
      equivTypV env n .boolT t
    | .lenE e1 => do
      let t1 ← inferExp env n e1
      let _ ← asListTyp "expression" env n t1
      validExp .rhs env n e1 t1
      equivTypV env n (.numT .nat) t
    | .tupE es => do
      let xts ← asTupTyp "tuple" env n t
      validTupExp side env n es xts Subst.empty
    | .callE x args => do
      let (ps, t', _) ← match env.findDef? x with
        | some d => pure d
        | none => err s!"undeclared definition {x}"
      let s ← validArgs env n args ps Subst.empty
      equivTypV env n (← liftS (Subst.substTypOpt s t')) t
    | .iterE e1 ie => do
      let (it, env') ← validIterexp side env n ie
      let t1 ← asIterTyp it "iteration" env n t
      validExp side env' n e1 t1
    | .projE e1 i => do
      let t1 ← inferExp env n e1
      let xts ← asTupTyp "expression" env n t1
      let side' := if xts.length > 1 then Side.rhs else side
      validExp side' env n e1 (.tupT xts)
      equivTypV env n (← projTupTyp n i xts e1) t
    | .uncaseE e1 op => do
      let t1 ← inferExp env n e1
      validExp side env n e1 t1
      validMixop env op
      match ← asVariantTypV "expression" env n t1 with
      | [.mk op' t' _ _] =>
        if eqMixop op op' then equivTypV env n t' t
        else err "invalid case projection"
      | _ => err "invalid case projection"
    | .optE eo => do
      let t1 ← asIterTyp .opt "option" env n t
      match eo with
      | none => pure ()
      | some e1 => validExp side env n e1 t1
    | .theE e1 => validExp side env n e1 (.iterT t .opt)
    | .listE es => do
      let t1 ← asIterTyp .list "list" env n t
      es.forM (fun eI => validExp side env n eI t1)
    | .liftE e1 => do
      let t1 ← asIterTyp .list "lifting" env n t
      validExp side env n e1 (.iterT t1 .opt)
    | .catE e1 e2 => do
      -- valid.ml:483-491: Lhs special case when either side is
      -- list-literal-shaped; guards fall through to the plain row
      let isListShape := fun (ex : Exp) => match ex.it with
        | .listE _ => true
        | .catE exi _ => (match exi.it with | .listE _ => true | _ => false)
        | _ => false
      let _ ← asIterTyp .list "list" env n t
      if side == .lhs && (isListShape e1 || isListShape e2) then do
        validExp side env n e1 t
        validExp side env n e2 t
      else do
        validExp .rhs env n e1 t
        validExp .rhs env n e2 t
    | .caseE op e1 => do
      let cases ← asVariantTypV "case" env n t
      let (t1, _, _) ← findCase cases op
      validMixop env op
      validExp side env n e1 t1
    | .ifE e1 e2 e3 => do
      validExp side env n e1 .boolT
      validExp side env n e2 t
      validExp side env n e3 t
    | .cvtE e1 nt1 nt2 => do
      validExp side env n e1 (.numT nt1)
      equivTypV env n (.numT nt2) t
    | .subE e1 t1 t2 => do
      validTyp env n t1
      validTyp env n t2
      validExp side env n e1 t1
      equivTypV env n t2 t
      subTypV env n t1 t2

/-- valid.ml:435-448 the TupE loop. -/
def validTupExp (side : Side) (env : Env) (fuel : Nat) :
    List Exp → List TypBind → Subst → EvalM Unit :=
  fun es xts s =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match es, xts with
    | [], [] => pure ()
    | eI :: es', .mk xI tI :: xts' => do
      validExp side env n eI (← liftS (Subst.substTypOpt s tI))
      validTupExp side env n es' xts' (Subst.addVarid s xI eI)
    | _, _ => err "arity mismatch for tuple"

/-- valid.ml:512-519 `valid_expmix`. -/
def validExpmix (side : Side) (env : Env) (fuel : Nat) (mixop : Mixop)
    (e : Exp) (expected : Mixop × Typ) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let (mixop', t) := expected
    if !eqMixop mixop mixop' then
      err s!"mixin notation {XlPrint.mixopToString mixop} does not match expected {XlPrint.mixopToString mixop'}"
    else do
      validMixop env mixop
      validExp side env n e t

/-- valid.ml:521-530 `valid_expfield`. -/
def validExpfield (side : Side) (env : Env) (fuel : Nat) (ef : ExpField)
    (tf : TypField) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match ef, tf with
    | .mk atom1 e, .mk atom2 t _ _ => do
      if !eqAtom atom1 atom2 then err "unexpected record field"
      else do
        validAtom env atom1
        validExp side env n e t

/-- valid.ml:532-555 `valid_path` (returns the target type; checks the
path's note against it). -/
def validPath (env : Env) (fuel : Nat) (p : Path) (t : Typ) : EvalM Typ :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    validTyp env n t
    let t' ← match p.it with
      | .rootP => pure t
      | .idxP p1 e1 => do
        let t1 ← validPath env n p1 t
        validExp .rhs env n e1 (.numT .nat)
        asListTyp "path" env n t1
      | .sliceP p1 e1 e2 => do
        let t1 ← validPath env n p1 t
        validExp .rhs env n e1 (.numT .nat)
        validExp .rhs env n e2 (.numT .nat)
        let _ ← asListTyp "path" env n t1
        pure t1
      | .dotP p1 atom => do
        let t1 ← validPath env n p1 t
        validAtom env atom
        let tfs ← asStructTypV "path" env n t1
        pure (← findField tfs atom).1
    equivTypV env n p.note t'
    pure t'

/-- valid.ml:560-594 `valid_sym` (returns the attribute type). -/
def validSym (env : Env) (fuel : Nat) (g : Sym) : EvalM Typ :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match g with
    | .varG x args => do
      let (ps, t, _) ← match env.findGram? x with
        | some d => pure d
        | none => err s!"undeclared grammar {x}"
      let s ← validArgs env n args ps Subst.empty
      liftS (Subst.substTypOpt s t)
    | .numG _ => pure (.numT .nat)
    | .textG _ => pure .textT
    | .epsG => pure (.tupT [])
    | .seqG gs => do
      let _ ← gs.mapM (validSym env n)
      pure (.tupT [])
    | .altG gs => do
      let _ ← gs.mapM (validSym env n)
      pure (.tupT [])
    | .rangeG g1 g2 => do
      let t1 ← validSym env n g1
      let t2 ← validSym env n g2
      equivTypV env n t1 (.numT .nat)
      equivTypV env n t2 (.numT .nat)
      pure (.numT .nat)
    | .iterG g1 ie => do
      let (it, env') ← validIterexp .lhs env n ie
      let t1 ← validSym env' n g1
      pure (.iterT t1 it)
    | .attrG e g1 => do
      let t1 ← validSym env n g1
      validExp .lhs env n e t1
      pure t1

/-- valid.ml:599-631 `valid_prem` (returns the extended env). -/
def validPrem (env : Env) (fuel : Nat) (prem : Prem) : EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prem with
    | .rulePr x args mixop e => do
      let (ps, mixop', t, _) ← match env.findRel? x with
        | some d => pure d
        | none => err s!"undeclared relation {x}"
      -- valid.ml:604 assert (Mixop.eq): fail closed instead
      if !eqMixop mixop mixop' then
        err "rule premise mixop mismatch (assert upstream, valid.ml:604)"
      else do
        let s ← validArgs env n args ps Subst.empty
        validExpmix .rhs env n mixop e (mixop, ← liftS (Subst.substTypOpt s t))
        pure env
    | .ifPr e => do
      validExp .rhs env n e .boolT
      pure env
    | .letPr qs e1 e2 => do
      let env' ← validQuants env n qs
      let t ← inferExp env n e2
      validExp .lhs env' n e1 t
      validExp .rhs env n e2 t
      let bound := Free.boundQuants qs
      let free := Free.freeExp e1
      if !(Sets.subset bound free) then
        err "quantified identifier(s) do not occur in left-hand side expression"
      else pure env'
    | .elsePr => pure env
    | .iterPr prem' ie => do
      let (_, env') ← validIterexp .rhs env n ie
      let _ ← validPrem env' n prem'
      pure env  -- valid.ml:630 TODO upstream: env, not env''
    | .negPr prem' => validPrem env n prem'

/-- valid.ml:633 `valid_prems`. -/
def validPrems (env : Env) (fuel : Nat) : List Prem → EvalM Env :=
  fun prems =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prems with
    | [] => pure env
    | prem :: prems' => do
      let env' ← validPrem env n prem
      validPrems env' n prems'

/-- valid.ml:638-662 `valid_arg` (extends the substitution). -/
def validArg (env : Env) (fuel : Nat) (a : Arg) (p : Param) (s : Subst) :
    EvalM Subst :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    let p' ← liftS (Subst.substParam s p)
    match a, p' with
    | .expA e, .expP x t => do
      validExp .lhs env n e t
      pure (Subst.addVarid s x e)
    | .typA t, .typP x => do
      validTyp env n t
      pure (Subst.addTypid s x t)
    | .defA x', .defP x ps t => do
      let (ps', t', _) ← match env.findDef? x' with
        | some d => pure d
        | none => err s!"undeclared definition {x'}"
      if ← equivFunctyp env n (ps', t') (ps, t) then
        pure (Subst.addDefid s x x')
      else err "type mismatch in function argument"
    | .gramA g, .gramP x [] t => do
      let t' ← validSym env n g
      equivTypV env n t' t
      pure (Subst.addGramid s x g)
    | .gramA g, .gramP x ps t => do
      match g with
      | .varG x' args' => do
        let (ps', t', _) ← match env.findGram? x' with
          | some d => pure d
          | none => err s!"undeclared grammar {x'}"
        if !args'.isEmpty then err "type mismatch in grammar argument"
        else if ← equivFunctyp env n (ps', t') (ps, t) then
          pure (Subst.addGramid s x g)
        else err "type mismatch in grammar argument"
      | _ => err "type mismatch in grammar argument"
    | _, _ => err "sort mismatch for argument"

/-- valid.ml:664-674 `valid_args`. -/
def validArgs (env : Env) (fuel : Nat) :
    List Arg → List Param → Subst → EvalM Subst :=
  fun args ps s =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match args, ps with
    | [], [] => pure s
    | _ :: _, [] => err "too many arguments"
    | [], _ :: _ => err "too few arguments"
    | a :: args', p :: ps' => do
      let s' ← validArg env n a p s
      validArgs env n args' ps' s'

/-- valid.ml:676-690 `valid_param` (returns the extended env). -/
def validParam (env : Env) (fuel : Nat) (p : Param) : EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match p with
    | .expP x t => do
      validTyp env n t
      pure (env.bindVar x t)
    | .typP x => pure (env.bindTyp x ([], []))
    | .defP x ps t => do
      let env' ← validParams env n ps
      validTyp env' n t
      pure (env.bindDef x (ps, t, []))
    | .gramP x ps t => do
      let env' ← validParams env n ps
      validTyp env' n t
      pure (env.bindGram x (ps, t, []))

/-- valid.ml:694-695 `valid_params`/`valid_quants` (binder folds). -/
def validParams (env : Env) (fuel : Nat) : List Param → EvalM Env :=
  fun ps =>
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match ps with
    | [] => pure env
    | p :: ps' => do validParams (← validParam env n p) n ps'

def validQuants (env : Env) (fuel : Nat) (qs : List Param) : EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => validParams env n qs

end

/-- valid.ml:697-706 `valid_inst`. -/
def validInst (env : Env) (fuel : Nat) (ps : List Param) (inst : Inst) :
    EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match inst with
    | .mk _ qs args dt => do
      let env' ← validQuants env n qs
      let _ ← validArgs env' n args ps Subst.empty
      validDeftyp env' n dt

/-- valid.ml:708-717 `valid_rule`. -/
def validRule (env : Env) (fuel : Nat) (mixop : Mixop) (t : Typ)
    (rule : Rule) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match rule with
    | .mk _ _ qs mixop' e prems => do
      let env' ← validQuants env n qs
      validExpmix .lhs env' n mixop' e (mixop, t)
      let _ ← validPrems env' n prems
      pure ()

/-- valid.ml:719-729 `valid_clause`. -/
def validClause (env : Env) (fuel : Nat) (ps : List Param) (t : Typ)
    (clause : Clause) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match clause with
    | .mk _ qs args e prems => do
      let env' ← validQuants env n qs
      let s ← validArgs env' n args ps Subst.empty
      let env'' ← validPrems env' n prems
      validExp .rhs env'' n e (← liftS (Subst.substTypOpt s t))

/-- valid.ml:731-741 `valid_prod`. -/
def validProd (env : Env) (fuel : Nat) (_ps : List Param) (t : Typ)
    (prod : Prod) : EvalM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match prod with
    | .mk _ qs g e prems => do
      let env' ← validQuants env n qs
      let _ ← validSym env' n g
      let env'' ← validPrems env' n prems
      validExp .rhs env'' n e t

/-- valid.ml:743-760 `infer_def`. -/
def inferDef (env : Env) (fuel : Nat) (d : Def) : EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match d with
    | .typD x _ ps _ => do
      let _ ← validParams env n ps
      pure (env.bindTyp x (ps, []))
    | .relD x _ ps op t rules => do
      let env' ← validParams env n ps
      validTyp env' n t
      pure (env.bindRel x (ps, op, t, rules))
    | .decD x _ ps t clauses => do
      let env' ← validParams env n ps
      validTyp env' n t
      pure (env.bindDef x (ps, t, clauses))
    | .gramD x _ ps t prods => do
      let env' ← validParams env n ps
      validTyp env' n t
      pure (env.bindGram x (ps, t, prods))
    | .recD _ _ => pure env

/-- valid.ml:763-802 `valid_def` (returns the extended env). -/
def validDef (env : Env) (fuel : Nat) (d : Def) : EvalM Env :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match d with
    | .typD x _ ps insts => do
      let env' ← validParams env n ps
      insts.forM (validInst env' n ps)
      pure (env.bindTyp x (ps, insts))
    | .relD x _ ps mixop t rules => do
      let env' ← validParams env n ps
      validTypcase env' n (.mk mixop t [] [])
      rules.forM (validRule env' n mixop t)
      pure (env.bindRel x (ps, mixop, t, rules))
    | .decD x _ ps t clauses => do
      let env' ← validParams env n ps
      validTyp env' n t
      clauses.forM (validClause env' n ps t)
      pure (env.bindDef x (ps, t, clauses))
    | .gramD x _ ps t prods => do
      let env' ← validParams env n ps
      validTyp env' n t
      prods.forM (validProd env' n ps t)
      pure (env.bindGram x (ps, t, prods))
    | .recD _ ds => do
      let env' ← ds.foldlM (fun e d1 => inferDef e n d1) env
      let env'' ← ds.foldlM (fun e d1 => validDef e n d1) env'
      -- valid.ml:786-799: same-sort recursion check
      let sortOf : Def → Nat := fun d1 => match d1 with
        | .typD _ _ _ _ => 0 | .relD _ _ _ _ _ _ => 1
        | .decD _ _ _ _ _ => 2 | .gramD _ _ _ _ _ => 3
        | .recD _ _ => 4
      match ds with
      | [] => pure env''
      | d0 :: _ =>
        if ds.all (fun d1 => sortOf d1 == sortOf d0) then pure env''
        else err "invalid recursion between definitions of different sort"

/-- valid.ml:807-808 `valid` (whole script). -/
def validScript (fuel : Nat) (ds : Script) : EvalM Unit := do
  let _ ← ds.foldlM (fun env d => validDef env fuel d) Env.empty
  pure ()

end Valid

end SpecTecLean.Il
