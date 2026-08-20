import SpecTecLean.Il.Ast
/-!
Structural equality: mirrors `deps/spectec/spectec/src/il/eq.ml` plus the
mixop machinery it uses (`xl/mixop.ml:54-78` — NOTE `Mixop.eq` is
FLATTEN-based, a quotient: e.g. `Seq [Atom a]` equals `Atom a`; arity of
trailing `Arg`s distinguishes, structure otherwise does not) and
`Atom.eq` (`xl/atom.ml:79-80`, `.it` equality — our `Atom` is bare, so
derived `BEq` is exactly it).

eq.ml compares `.it` ONLY — notes and regions are ignored — hence these
functions instead of the note-sensitive derived `BEq` on `Exp`.

Deliberate divergence (logged): eq.ml's fallback `e1.it = e2.it` uses
OCaml POLYMORPHIC equality, which for the two composite constructors that
lack explicit cases — `IfE` (eq.ml:68-107 omits it) and `NegPr`
(eq.ml:143-152 omits it) — deep-compares nested phrases INCLUDING regions
and notes: almost certainly an upstream oversight (both were added late),
and unmirrorable anyway (we don't carry expression regions). We treat
both like their sibling constructors (recursive, note-insensitive) —
candidate upstream report.
-/

namespace SpecTecLean.Il

namespace MixopEq

open SpecTecLean.Xl

/-- mixop.ml:54-57 the local `(++)` merge: last group of the left fuses
with first group of the right. Inputs are never `[]` for flatten output
(minimum is `[[]]`); the `[]` cases are unreachable-but-total. -/
def merge (a b : List (List Atom)) : List (List Atom) :=
  match a, b with
  | [], b => b
  | a, [] => a
  | _, _ =>
    let a' := a.dropLast
    let la := a.getLast!
    match b with
    | hb :: b' => a' ++ [la ++ hb] ++ b'
    | [] => a

/-- mixop.ml:67-72 `flatten`. -/
def flatten : Mixop → List (List Atom)
  | .arg => [[], []]
  | .atom a => [[a]]
  | .brack l m r => merge (merge [[l]] (flatten m)) [[r]]
  | .infix m1 a m2 => merge (merge (flatten m1) [[a]]) (flatten m2)
  | .seq ms => ms.attach.foldl (fun acc ⟨m, _⟩ => merge acc (flatten m)) [[]]

end MixopEq

/-- mixop.ml:74-78 `eq` via `flatten` comparison (`Atom.compare` is `.it`
comparison, equality-equivalent to our derived `BEq`). -/
def eqMixop (m1 m2 : Mixop) : Bool :=
  MixopEq.flatten m1 == MixopEq.flatten m2

/-- eq.ml:25-26 `eq_atom` (= `Atom.eq` = `.it` equality). -/
def eqAtom (a1 a2 : Atom) : Bool := a1 == a2

/-- eq.ml:22-23 `eq_id`. -/
def eqId (x1 x2 : Id) : Bool := x1 == x2

mutual

/-- eq.ml:34-37 `eq_iter`. -/
def eqIter : Iter → Iter → Bool
  | .listN e1 xo1, .listN e2 xo2 => eqExp e1 e2 && xo1 == xo2
  | .opt, .opt | .list, .list | .list1, .list1 => true
  | _, _ => false

/-- eq.ml:42-48 `eq_typ`. -/
def eqTyp (t1 t2 : Typ) : Bool :=
  match t1, t2 with
  | .varT x1 as1, .varT x2 as2 => eqId x1 x2 && eqArgs as1 as2
  | .tupT xts1, .tupT xts2 => eqTypbinds xts1 xts2
  | .iterT t11 it1, .iterT t21 it2 => eqTyp t11 t21 && eqIter it1 it2
  | .boolT, .boolT | .textT, .textT => true
  | .numT nt1, .numT nt2 => nt1 == nt2
  | _, _ => false

def eqTypbinds : List TypBind → List TypBind → Bool
  | [], [] => true
  | .mk x1 t1 :: r1, .mk x2 t2 :: r2 =>
    eqId x1 x2 && eqTyp t1 t2 && eqTypbinds r1 r2
  | _, _ => false

/-- eq.ml:50-55 `eq_deftyp`. -/
def eqDeftyp : DefTyp → DefTyp → Bool
  | .aliasT t1, .aliasT t2 => eqTyp t1 t2
  | .structT f1, .structT f2 => eqTypfields f1 f2
  | .variantT c1, .variantT c2 => eqTypcases c1 c2
  | _, _ => false

/-- eq.ml:57-59 `eq_typfield` (hints ignored upstream too). -/
def eqTypfields : List TypField → List TypField → Bool
  | [], [] => true
  | .mk a1 t1 q1 p1 :: r1, .mk a2 t2 q2 p2 :: r2 =>
    eqAtom a1 a2 && eqTyp t1 t2 && eqParams q1 q2 && eqPrems p1 p2
      && eqTypfields r1 r2
  | _, _ => false

/-- eq.ml:61-63 `eq_typcase`. -/
def eqTypcases : List TypCase → List TypCase → Bool
  | [], [] => true
  | .mk o1 t1 q1 p1 :: r1, .mk o2 t2 q2 p2 :: r2 =>
    eqMixop o1 o2 && eqTyp t1 t2 && eqParams q1 q2 && eqPrems p1 p2
      && eqTypcases r1 r2
  | _, _ => false

/-- eq.ml:68-107 `eq_exp` (`.it` only — notes ignored). -/
def eqExp : Exp → Exp → Bool
  | .mk it1 _, .mk it2 _ => eqExp' it1 it2

def eqExp' : Exp' → Exp' → Bool
  | .varE x1, .varE x2 => eqId x1 x2
  | .unE op1 ot1 e1, .unE op2 ot2 e2 =>
    op1 == op2 && ot1 == ot2 && eqExp e1 e2
  | .binE op1 ot1 e11 e12, .binE op2 ot2 e21 e22 =>
    op1 == op2 && ot1 == ot2 && eqExp e11 e21 && eqExp e12 e22
  | .cmpE op1 ot1 e11 e12, .cmpE op2 ot2 e21 e22 =>
    op1 == op2 && ot1 == ot2 && eqExp e11 e21 && eqExp e12 e22
  | .liftE e1, .liftE e2 | .lenE e1, .lenE e2 => eqExp e1 e2
  | .idxE e11 e12, .idxE e21 e22 | .compE e11 e12, .compE e21 e22
  | .memE e11 e12, .memE e21 e22 | .catE e11 e12, .catE e21 e22 =>
    eqExp e11 e21 && eqExp e12 e22
  | .sliceE e11 e12 e13, .sliceE e21 e22 e23 =>
    eqExp e11 e21 && eqExp e12 e22 && eqExp e13 e23
  | .updE e11 p1 e12, .updE e21 p2 e22
  | .extE e11 p1 e12, .extE e21 p2 e22 =>
    eqExp e11 e21 && eqPath p1 p2 && eqExp e12 e22
  | .tupE es1, .tupE es2 | .listE es1, .listE es2 => eqExps es1 es2
  | .strE efs1, .strE efs2 => eqExpfields efs1 efs2
  | .dotE e1 a1, .dotE e2 a2 => eqExp e1 e2 && eqAtom a1 a2
  | .uncaseE e1 op1, .uncaseE e2 op2 => eqMixop op1 op2 && eqExp e1 e2
  | .callE x1 as1, .callE x2 as2 => eqId x1 x2 && eqArgs as1 as2
  | .iterE e1 it1, .iterE e2 it2 => eqExp e1 e2 && eqIterexp it1 it2
  | .optE none, .optE none => true
  | .optE (some e1), .optE (some e2) => eqExp e1 e2
  | .projE e1 i1, .projE e2 i2 => eqExp e1 e2 && i1 == i2
  | .theE e1, .theE e2 => eqExp e1 e2
  | .caseE op1 e1, .caseE op2 e2 => eqMixop op1 op2 && eqExp e1 e2
  | .cvtE e1 nt11 nt12, .cvtE e2 nt21 nt22 =>
    eqExp e1 e2 && nt11 == nt21 && nt12 == nt22
  | .subE e1 t11 t12, .subE e2 t21 t22 =>
    eqExp e1 e2 && eqTyp t11 t21 && eqTyp t12 t22
  -- eq.ml has NO IfE case (falls to polymorphic =); divergence, see header
  | .ifE e11 e12 e13, .ifE e21 e22 e23 =>
    eqExp e11 e21 && eqExp e12 e22 && eqExp e13 e23
  -- leaves reached by eq.ml's `e1.it = e2.it` fallback
  | .boolE b1, .boolE b2 => b1 == b2
  | .numE n1, .numE n2 => n1 == n2
  | .textE t1, .textE t2 => t1 == t2
  | _, _ => false

def eqExps : List Exp → List Exp → Bool
  | [], [] => true
  | e1 :: r1, e2 :: r2 => eqExp e1 e2 && eqExps r1 r2
  | _, _ => false

/-- eq.ml:109-110 `eq_expfield`. -/
def eqExpfields : List ExpField → List ExpField → Bool
  | [], [] => true
  | .mk a1 e1 :: r1, .mk a2 e2 :: r2 =>
    eqAtom a1 a2 && eqExp e1 e2 && eqExpfields r1 r2
  | _, _ => false

/-- eq.ml:112-120 `eq_path`. -/
def eqPath : Path → Path → Bool
  | .mk it1 _, .mk it2 _ => eqPath' it1 it2

def eqPath' : Path' → Path' → Bool
  | .rootP, .rootP => true
  | .idxP p1 e1, .idxP p2 e2 => eqPath p1 p2 && eqExp e1 e2
  | .sliceP p1 e11 e12, .sliceP p2 e21 e22 =>
    eqPath p1 p2 && eqExp e11 e21 && eqExp e12 e22
  | .dotP p1 a1, .dotP p2 a2 => eqPath p1 p2 && eqAtom a1 a2
  | _, _ => false

/-- eq.ml:122-123 `eq_iterexp`. -/
def eqIterexp : IterExp → IterExp → Bool
  | .mk it1 xes1, .mk it2 xes2 => eqIter it1 it2 && eqDoms xes1 xes2

def eqDoms : List Dom → List Dom → Bool
  | [], [] => true
  | .mk x1 e1 :: r1, .mk x2 e2 :: r2 =>
    eqId x1 x2 && eqExp e1 e2 && eqDoms r1 r2
  | _, _ => false

/-- eq.ml:128-138 `eq_sym`. -/
def eqSym : Sym → Sym → Bool
  | .varG x1 as1, .varG x2 as2 => eqId x1 x2 && eqArgs as1 as2
  | .seqG gs1, .seqG gs2 | .altG gs1, .altG gs2 => eqSyms gs1 gs2
  | .rangeG g11 g12, .rangeG g21 g22 => eqSym g11 g21 && eqSym g12 g22
  | .iterG g1 it1, .iterG g2 it2 => eqSym g1 g2 && eqIterexp it1 it2
  | .attrG e1 g1, .attrG e2 g2 => eqExp e1 e2 && eqSym g1 g2
  | .numG n1, .numG n2 => n1 == n2
  | .textG t1, .textG t2 => t1 == t2
  | .epsG, .epsG => true
  | _, _ => false

def eqSyms : List Sym → List Sym → Bool
  | [], [] => true
  | g1 :: r1, g2 :: r2 => eqSym g1 g2 && eqSyms r1 r2
  | _, _ => false

/-- eq.ml:143-152 `eq_prem` (NegPr divergence, see header). -/
def eqPrem : Prem → Prem → Bool
  | .rulePr x1 as1 op1 e1, .rulePr x2 as2 op2 e2 =>
    eqId x1 x2 && eqArgs as1 as2 && eqMixop op1 op2 && eqExp e1 e2
  | .ifPr e1, .ifPr e2 => eqExp e1 e2
  | .iterPr pr1 it1, .iterPr pr2 it2 => eqPrem pr1 pr2 && eqIterexp it1 it2
  | .letPr q1 e11 e12, .letPr q2 e21 e22 =>
    eqParams q1 q2 && eqExp e11 e21 && eqExp e12 e22
  | .negPr pr1, .negPr pr2 => eqPrem pr1 pr2
  | .elsePr, .elsePr => true
  | _, _ => false

def eqPrems : List Prem → List Prem → Bool
  | [], [] => true
  | p1 :: r1, p2 :: r2 => eqPrem p1 p2 && eqPrems r1 r2
  | _, _ => false

/-- eq.ml:157-163 `eq_arg`. -/
def eqArg : Arg → Arg → Bool
  | .expA e1, .expA e2 => eqExp e1 e2
  | .typA t1, .typA t2 => eqTyp t1 t2
  | .defA x1, .defA x2 => eqId x1 x2
  | .gramA g1, .gramA g2 => eqSym g1 g2
  | _, _ => false

def eqArgs : List Arg → List Arg → Bool
  | [], [] => true
  | a1 :: r1, a2 :: r2 => eqArg a1 a2 && eqArgs r1 r2
  | _, _ => false

/-- eq.ml:165-173 `eq_param`. -/
def eqParam : Param → Param → Bool
  | .expP x1 t1, .expP x2 t2 => eqId x1 x2 && eqTyp t1 t2
  | .typP x1, .typP x2 => eqId x1 x2
  | .defP x1 ps1 t1, .defP x2 ps2 t2 =>
    eqId x1 x2 && eqParams ps1 ps2 && eqTyp t1 t2
  | .gramP x1 ps1 t1, .gramP x2 ps2 t2 =>
    eqId x1 x2 && eqParams ps1 ps2 && eqTyp t1 t2
  | _, _ => false

def eqParams : List Param → List Param → Bool
  | [], [] => true
  | p1 :: r1, p2 :: r2 => eqParam p1 p2 && eqParams r1 r2
  | _, _ => false

end

end SpecTecLean.Il
