import SpecTecLean.Il.Ast
import SpecTecLean.Il.Free
import SpecTecLean.Il.Fresh
import SpecTecLean.Il.Env
/-!
Capture-avoiding substitution, mirroring
`deps/spectec/spectec/src/il/subst.ml` (spectec @ acc6e834).

Monad: `SubstM = StateT Fresh.St (Except String)`. The state mirrors
fresh.ml's global counters (see Il/Fresh.lean divergence note); the error
layer makes subst.ml's partial spots fail closed instead of raising:
`subst_gramid` on a non-`VarG(x,[])` image (subst.ml:75
`Invalid_argument`), the higher-order-substitution assert (subst.ml:113),
and the CaseE/UncaseE note asserts (subst.ml:182,190).

Structural divergences (logged): subst.ml:85-103's polymorphic
`subst_iterexp` helper is INLINED at its three call sites (IterE, IterG,
IterPr) — higher-order recursion defeats Lean's termination checker — and
its `subst_iter s it'` call on the REBUILT iter is fused with the
refresh match (the composition is identical: for `ListN(e, Some x)` the
rebuilt iter's substitution is exactly `ListN(subst_exp s e, Some x')`).
Likewise `subst_list_dep` (subst.ml:56-61) is specialized
(`substParamsDep`, `substPrems`).
-/

namespace SpecTecLean.Il

/-- subst.ml:9-11 `subst`. -/
structure Subst where
  varid : SMap Exp := {}
  typid : SMap Typ := {}
  defid : SMap Id := {}
  gramid : SMap Sym := {}
deriving Inhabited

namespace Subst

def empty : Subst := {}

/-- The `s = empty` optimization guards (subst.ml:280-284). -/
def isEmpty (s : Subst) : Bool :=
  s.varid.entries.isEmpty && s.typid.entries.isEmpty
    && s.defid.entries.isEmpty && s.gramid.entries.isEmpty

/-- subst.ml:30-33 `add_*` (`"_"` never bound). -/
def addVarid (s : Subst) (x : Id) (e : Exp) : Subst :=
  if x == "_" then s else { s with varid := s.varid.add x e }
def addTypid (s : Subst) (x : Id) (t : Typ) : Subst :=
  if x == "_" then s else { s with typid := s.typid.add x t }
def addDefid (s : Subst) (x : Id) (x' : Id) : Subst :=
  if x == "_" then s else { s with defid := s.defid.add x x' }
def addGramid (s : Subst) (x : Id) (g : Sym) : Subst :=
  if x == "_" then s else { s with gramid := s.gramid.add x g }

/-- subst.ml:47 `remove_varid'`. -/
def removeVarid (s : Subst) (x : String) : Subst :=
  { s with varid := ⟨s.varid.entries.filter (fun p => p.1 != x)⟩ }

/-- subst.ml:48 `remove_varids` (over a free-var set). -/
def removeVarids (s : Subst) (xs : IdSet) : Subst :=
  xs.foldl removeVarid s

end Subst

/-- See header. -/
abbrev SubstM := StateT Fresh.St (Except String)

namespace Subst

/-- subst.ml:66-69 `subst_defid`. -/
def substDefid (s : Subst) (x : Id) : Id :=
  match s.defid.find? x with
  | none => x
  | some x' => x'

/-- subst.ml:71-75 `subst_gramid` (raise → fail closed). -/
def substGramid (s : Subst) (x : Id) : SubstM Id :=
  match s.gramid.find? x with
  | none => pure x
  | some (.varG x' []) => pure x'
  | some _ => throw "subst_gramid: non-variable grammar substitution (Invalid_argument upstream, subst.ml:75)"

/-- The refreshed dom pair carried by the inlined iterexp handling:
subst.ml:95-100. -/
private def iterexpSubstExt (xxts : List (Id × Id × Typ)) (s : Subst) :
    Subst :=
  xxts.foldl (fun s xxt =>
    let (x, x', t) := xxt
    s.addVarid x (.mk (.varE x') t)) s

mutual

/-- subst.ml:80-83 `subst_iter`. -/
def substIter (s : Subst) (it : Iter) : SubstM Iter :=
  match it with
  | .opt => pure .opt
  | .list => pure .list
  | .list1 => pure .list1
  | .listN e xo => do pure (.listN (← substExp s e) xo)
  termination_by sizeOf it

/-- subst.ml:108-118 `subst_typ`. -/
def substTyp (s : Subst) (t : Typ) : SubstM Typ :=
  match t with
  | .varT x args =>
    match s.typid.find? x with
    | none => do pure (.varT x (← args.attach.mapM (fun ⟨a, _⟩ => substArg s a)))
    | some t' =>
      -- subst.ml:113: higher-order substitution unsupported (assert)
      if args.isEmpty then pure t'
      else throw "substTyp: higher-order type substitution (assert upstream, subst.ml:113)"
  | .boolT => pure .boolT
  | .numT nt => pure (.numT nt)
  | .textT => pure .textT
  | .tupT xts => do pure (.tupT (← substTupTyp s xts).1)
  | .iterT t1 it => do pure (.iterT (← substTyp s t1) (← substIter s it))
  termination_by sizeOf t

/-- subst.ml:120-123 `subst_typ'` (returns the extended subst). -/
def substTyp' (s : Subst) (t : Typ) : SubstM (Typ × Subst) :=
  match t with
  | .tupT xts => do
    let (xts', s') ← substTupTyp s xts
    pure (.tupT xts', s')
  | t => do pure (← substTyp s t, s)

/-- subst.ml:125-132 `subst_tup_typ` (refreshes tuple binders). -/
def substTupTyp (s : Subst) (xts : List TypBind) :
    SubstM (List TypBind × Subst) :=
  match xts with
  | [] => pure ([], s)
  | .mk x t :: xts => do
    let x' ← Fresh.refreshVarid x
    let t' ← substTyp s t
    let s' := s.addVarid x (.mk (.varE x') t')
    let (xts', s'') ← substTupTyp s' xts
    pure (.mk x' t' :: xts', s'')
  termination_by sizeOf xts

/-- subst.ml:134-139 `subst_deftyp`. -/
def substDeftyp (s : Subst) (dt : DefTyp) : SubstM DefTyp :=
  match dt with
  | .aliasT t => do pure (.aliasT (← substTyp s t))
  | .structT tfs => do
    pure (.structT (← tfs.attach.mapM (fun ⟨f, _⟩ => substTypfield s f)))
  | .variantT tcs => do
    pure (.variantT (← tcs.attach.mapM (fun ⟨c, _⟩ => substTypcase s c)))

/-- subst.ml:141-144 `subst_typfield`. -/
def substTypfield (s : Subst) (f : TypField) : SubstM TypField :=
  match f with
  | .mk atom t qs prems => do
    let (t', s') ← substTyp' s t
    let (qs', s'') ← substParamsDep s' qs
    pure (.mk atom t' qs' (← substPrems s'' prems))

/-- subst.ml:146-149 `subst_typcase`. -/
def substTypcase (s : Subst) (c : TypCase) : SubstM TypCase :=
  match c with
  | .mk op t qs prems => do
    let (t', s') ← substTyp' s t
    let (qs', s'') ← substParamsDep s' qs
    pure (.mk op t' qs' (← substPrems s'' prems))

/-- subst.ml:154-195 `subst_exp`. The note is substituted too
(subst.ml:195); a substituted `VarE` keeps the IMAGE's `.it` under the
ORIGINAL note's substitution (subst.ml:157-160,195). -/
def substExp (s : Subst) (e : Exp) : SubstM Exp :=
  match e with
  | .mk it note => do
    let it' ← substExp' s note it
    pure (.mk it' (← substTyp s note))
  termination_by sizeOf e

/-- `.it` part of subst.ml:154-195; `note` is the whole exp's note
(consulted by the CaseE assert, subst.ml:190). -/
def substExp' (s : Subst) (note : Typ) (it : Exp') : SubstM Exp' :=
  match it with
  | .varE x =>
    match s.varid.find? x with
    | none => pure (.varE x)
    | some e' => pure e'.it
  | .boolE b => pure (.boolE b)
  | .numE n => pure (.numE n)
  | .textE t => pure (.textE t)
  | .unE op ot e1 => do pure (.unE op ot (← substExp s e1))
  | .binE op ot e1 e2 => do
    pure (.binE op ot (← substExp s e1) (← substExp s e2))
  | .cmpE op ot e1 e2 => do
    pure (.cmpE op ot (← substExp s e1) (← substExp s e2))
  | .idxE e1 e2 => do pure (.idxE (← substExp s e1) (← substExp s e2))
  | .sliceE e1 e2 e3 => do
    pure (.sliceE (← substExp s e1) (← substExp s e2) (← substExp s e3))
  | .updE e1 p e2 => do
    pure (.updE (← substExp s e1) (← substPath s p) (← substExp s e2))
  | .extE e1 p e2 => do
    pure (.extE (← substExp s e1) (← substPath s p) (← substExp s e2))
  | .strE efs => do
    pure (.strE (← efs.attach.mapM (fun ⟨f, _⟩ => substExpfield s f)))
  | .dotE e1 atom => do pure (.dotE (← substExp s e1) atom)
  | .compE e1 e2 => do pure (.compE (← substExp s e1) (← substExp s e2))
  | .memE e1 e2 => do pure (.memE (← substExp s e1) (← substExp s e2))
  | .lenE e1 => do pure (.lenE (← substExp s e1))
  | .tupE es => do
    pure (.tupE (← es.attach.mapM (fun ⟨e1, _⟩ => substExp s e1)))
  | .callE x args => do
    pure (.callE (substDefid s x)
      (← args.attach.mapM (fun ⟨a, _⟩ => substArg s a)))
  | .iterE e1 (.mk itr xes) => do
    -- INLINED subst_iterexp (subst.ml:85-103) at f = subst_exp; the
    -- rebuilt iter's substitution is fused (see header)
    let (it'', xxts1) ← match itr with
      | .listN e (some x) => do
        let x' ← Fresh.refreshVarid x
        pure (Iter.listN (← substExp s e) (some x'),
              [(x, x', Typ.numT .nat)])
      | itr => do pure (← substIter s itr, ([] : List (Id × Id × Typ)))
    let xes' ← xes.attach.mapM (fun ⟨d, _⟩ => substDom s d)
    let xxts := (xes.zip xes').map (fun (d, d') =>
      match d, d' with
      | .mk x _, .mk x' e' => (x, x', e'.note))
    let s' := iterexpSubstExt (xxts1 ++ xxts) s
    pure (.iterE (← substExp s' e1) (.mk it'' xes'))
  | .projE e1 i => do pure (.projE (← substExp s e1) i)
  | .uncaseE e1 op => do
    -- subst.ml:180-183: assert the substituted argument's note is a VarT
    let e1' ← substExp s e1
    match e1'.note with
    | .varT _ _ => pure (.uncaseE e1' op)
    | _ => throw "substExp: UncaseE argument note not a VarT (assert upstream, subst.ml:182)"
  | .optE none => pure (.optE none)
  | .optE (some e1) => do pure (.optE (some (← substExp s e1)))
  | .theE e1 => do pure (.theE (← substExp s e1))
  | .listE es => do
    pure (.listE (← es.attach.mapM (fun ⟨e1, _⟩ => substExp s e1)))
  | .liftE e1 => do pure (.liftE (← substExp s e1))
  | .catE e1 e2 => do pure (.catE (← substExp s e1) (← substExp s e2))
  | .caseE op e1 => do
    -- subst.ml:189-191: assert the WHOLE exp's note is a VarT
    match note with
    | .varT _ _ => do pure (.caseE op (← substExp s e1))
    | _ => throw "substExp: CaseE note not a VarT (assert upstream, subst.ml:190)"
  | .cvtE e1 nt1 nt2 => do pure (.cvtE (← substExp s e1) nt1 nt2)
  | .subE e1 t1 t2 => do
    pure (.subE (← substExp s e1) (← substTyp s t1) (← substTyp s t2))
  | .ifE e1 e2 e3 => do
    pure (.ifE (← substExp s e1) (← substExp s e2) (← substExp s e3))
  termination_by sizeOf it

/-- subst.ml:95 the per-dom refresh+subst step of `subst_iterexp`. -/
def substDom (s : Subst) (d : Dom) : SubstM Dom :=
  match d with
  | .mk x e => do pure (Dom.mk (← Fresh.refreshVarid x) (← substExp s e))
  termination_by sizeOf d

/-- subst.ml:197 `subst_expfield`. -/
def substExpfield (s : Subst) (f : ExpField) : SubstM ExpField :=
  match f with
  | .mk atom e => do pure (.mk atom (← substExp s e))
  termination_by sizeOf f

/-- subst.ml:199-206 `subst_path` (note substituted, subst.ml:206). -/
def substPath (s : Subst) (p : Path) : SubstM Path :=
  match p with
  | .mk it note => do pure (.mk (← substPath' s it) (← substTyp s note))
  termination_by sizeOf p

def substPath' (s : Subst) (it : Path') : SubstM Path' :=
  match it with
  | .rootP => pure .rootP
  | .idxP p1 e => do pure (.idxP (← substPath s p1) (← substExp s e))
  | .sliceP p1 e1 e2 => do
    pure (.sliceP (← substPath s p1) (← substExp s e1) (← substExp s e2))
  | .dotP p1 atom => do pure (.dotP (← substPath s p1) atom)
  termination_by sizeOf it

/-- subst.ml:211-228 `subst_sym`. -/
def substSym (s : Subst) (g : Sym) : SubstM Sym :=
  match g with
  | .varG x [] =>
    match s.gramid.find? x with
    | none => pure (.varG x [])
    | some g' => pure g'
  | .varG x args => do
    pure (.varG (← substGramid s x)
      (← args.attach.mapM (fun ⟨a, _⟩ => substArg s a)))
  | .numG n => pure (.numG n)
  | .textG t => pure (.textG t)
  | .epsG => pure .epsG
  | .seqG gs => do
    pure (.seqG (← gs.attach.mapM (fun ⟨g1, _⟩ => substSym s g1)))
  | .altG gs => do
    pure (.altG (← gs.attach.mapM (fun ⟨g1, _⟩ => substSym s g1)))
  | .rangeG g1 g2 => do pure (.rangeG (← substSym s g1) (← substSym s g2))
  | .iterG g1 (.mk itr xes) => do
    -- INLINED subst_iterexp (subst.ml:85-103) at f = subst_sym
    let (it'', xxts1) ← match itr with
      | .listN e (some x) => do
        let x' ← Fresh.refreshVarid x
        pure (Iter.listN (← substExp s e) (some x'),
              [(x, x', Typ.numT .nat)])
      | itr => do pure (← substIter s itr, ([] : List (Id × Id × Typ)))
    let xes' ← xes.attach.mapM (fun ⟨d, _⟩ => substDom s d)
    let xxts := (xes.zip xes').map (fun (d, d') =>
      match d, d' with
      | .mk x _, .mk x' e' => (x, x', e'.note))
    let s' := iterexpSubstExt (xxts1 ++ xxts) s
    pure (.iterG (← substSym s' g1) (.mk it'' xes'))
  | .attrG e g1 => do pure (.attrG (← substExp s e) (← substSym s g1))
  termination_by sizeOf g

/-- subst.ml:233-245 `subst_prem`. -/
def substPrem (s : Subst) (pr : Prem) : SubstM Prem :=
  match pr with
  | .rulePr x args op e => do
    pure (.rulePr x (← args.attach.mapM (fun ⟨a, _⟩ => substArg s a)) op
      (← substExp s e))
  | .ifPr e => do pure (.ifPr (← substExp s e))
  | .elsePr => pure .elsePr
  | .iterPr prem1 (.mk itr xes) => do
    -- INLINED subst_iterexp (subst.ml:85-103) at f = subst_prem
    let (it'', xxts1) ← match itr with
      | .listN e (some x) => do
        let x' ← Fresh.refreshVarid x
        pure (Iter.listN (← substExp s e) (some x'),
              [(x, x', Typ.numT .nat)])
      | itr => do pure (← substIter s itr, ([] : List (Id × Id × Typ)))
    let xes' ← xes.attach.mapM (fun ⟨d, _⟩ => substDom s d)
    let xxts := (xes.zip xes').map (fun (d, d') =>
      match d, d' with
      | .mk x _, .mk x' e' => (x, x', e'.note))
    let s' := iterexpSubstExt (xxts1 ++ xxts) s
    pure (.iterPr (← substPrem s' prem1) (.mk it'' xes'))
  | .letPr qs e1 e2 => do
    -- subst.ml:241-243: binders shadow in e1, NOT in e2; qs unchanged
    let s' := s.removeVarids (Free.boundQuants qs).varid
    pure (.letPr qs (← substExp s' e1) (← substExp s e2))
  | .negPr prem1 => do pure (.negPr (← substPrem s prem1))
  termination_by sizeOf pr

/-- subst.ml:247-248 `subst_prems` (= subst_list_dep at bound_prem). -/
def substPrems (s : Subst) (prs : List Prem) : SubstM (List Prem) :=
  match prs with
  | [] => pure []
  | pr :: prs => do
    let pr' ← substPrem s pr
    let prs' ← substPrems (s.removeVarids (Free.boundPrem pr).varid) prs
    pure (pr' :: prs')
  termination_by sizeOf prs

/-- subst.ml:253-259 `subst_arg`. -/
def substArg (s : Subst) (a : Arg) : SubstM Arg :=
  match a with
  | .expA e => do pure (.expA (← substExp s e))
  | .typA t => do pure (.typA (← substTyp s t))
  | .defA x => pure (.defA (substDefid s x))
  | .gramA g => do pure (.gramA (← substSym s g))
  termination_by sizeOf a

/-- subst.ml:261-271 `subst_param`. -/
def substParam (s : Subst) (p : Param) : SubstM Param :=
  match p with
  | .expP x t => do pure (.expP x (← substTyp s t))
  | .typP x => pure (.typP x)
  | .defP x ps t => do
    let (ps', s') ← substParamsDep s ps
    pure (.defP x ps' (← substTyp s' t))
  | .gramP x ps t => do
    let (ps', s') ← substParamsDep s ps
    pure (.gramP x ps' (← substTyp s' t))
  termination_by sizeOf p

/-- subst.ml:274-275 `subst_params`/`subst_quants`
(= subst_list_dep at bound_param; bound_quant = bound_param). -/
def substParamsDep (s : Subst) (ps : List Param) :
    SubstM (List Param × Subst) :=
  match ps with
  | [] => pure ([], s)
  | p :: ps => do
    let p' ← substParam s p
    let (ps', s') ←
      substParamsDep (s.removeVarids (Free.boundParam p).varid) ps
    pure (p' :: ps', s')
  termination_by sizeOf ps

end

/-- subst.ml:280-284 optimization wrappers. -/
def substTypOpt (s : Subst) (t : Typ) : SubstM Typ :=
  if s.isEmpty then pure t else substTyp s t
def substDeftypOpt (s : Subst) (dt : DefTyp) : SubstM DefTyp :=
  if s.isEmpty then pure dt else substDeftyp s dt
def substExpOpt (s : Subst) (e : Exp) : SubstM Exp :=
  if s.isEmpty then pure e else substExp s e
def substSymOpt (s : Subst) (g : Sym) : SubstM Sym :=
  if s.isEmpty then pure g else substSym s g
def substPremsOpt (s : Subst) (prs : List Prem) : SubstM (List Prem) :=
  if s.isEmpty then pure prs else substPrems s prs

end Subst

end SpecTecLean.Il
