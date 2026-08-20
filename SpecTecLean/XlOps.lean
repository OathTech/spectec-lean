import SpecTecLean.Xl
import SpecTecLean.Il.Ast
/-!
Numeric/boolean operator semantics and atom/mixop rendering, mirroring
`deps/spectec/spectec/src/xl/num.ml`, `xl/bool.ml`, `xl/atom.ml:111-184`
(`to_string`) and `xl/mixop.ml:81-93` (`to_string`). The string renderers
are SEMANTIC here: valid.ml keys duplicate-detection and disjointness
sets on them (valid.ml:156-165, eval.ml:1171-1172).

Deliberate divergences (logged):
- `Real` arithmetic rows return `none` and are never consulted: the Eval
  layer throws BEFORE reaching them (raw-token representation, zero
  corpus coverage — see Il/Ast.lean). `narrow`/`widen` (num.ml:98-112)
  are unmirrored (no consumer in il/).
- Rationals are canonical `Int × Int` pairs (den > 0, reduced), matching
  zarith `Q.t`'s invariants; operations normalize like zarith does.
- `PowOp` on huge exponents: OCaml `Z.to_int` raises; we compute totally
  (the cgroup cap bounds the blast radius). num.ml:163-166.
-/

namespace SpecTecLean.Il

/-! ## Canonical rationals (zarith Q.t invariants) -/

namespace Rat

/-- Normalize to den > 0, gcd 1 (zarith `Q.make`). den = 0 is the
caller's responsibility to exclude (Q.t undef/inf unreachable here). -/
def mk (p q : Int) : Int × Int :=
  if q == 0 then (0, 0) -- unreachable by construction; loud garbage
  else
    let g : Nat := Nat.gcd p.natAbs q.natAbs
    let sign : Int := if q < 0 then -1 else 1
    (sign * p / g, sign * q / g)

def ofInt (i : Int) : Int × Int := (i, 1)
def add : Int × Int → Int × Int → Int × Int
  | (p1, q1), (p2, q2) => mk (p1 * q2 + p2 * q1) (q1 * q2)
def sub : Int × Int → Int × Int → Int × Int
  | (p1, q1), (p2, q2) => mk (p1 * q2 - p2 * q1) (q1 * q2)
def mul : Int × Int → Int × Int → Int × Int
  | (p1, q1), (p2, q2) => mk (p1 * p2) (q1 * q2)
def div : Int × Int → Int × Int → Int × Int
  | (p1, q1), (p2, q2) => mk (p1 * q2) (q1 * p2)
def neg : Int × Int → Int × Int | (p, q) => (-p, q)
def abs : Int × Int → Int × Int | (p, q) => (p.natAbs, q)
/-- q1 < q2 ⟺ p1·d2 < p2·d1 (dens positive). -/
def lt : Int × Int → Int × Int → Bool
  | (p1, q1), (p2, q2) => p1 * q2 < p2 * q1
def le (a b : Int × Int) : Bool := lt a b || a == b

end Rat

/-! ## num.ml operator semantics -/

namespace NumOps

/-- num.ml:60-64 `to_typ`. -/
def toTyp : Num → NumTyp
  | .nat _ => .nat
  | .int _ => .int
  | .rat _ _ => .rat
  | .real _ => .real

/-- num.ml:50-57 `sub` (numeric subtyping). -/
def subNumTyp (t1 t2 : NumTyp) : Bool :=
  match t1, t2 with
  | _, .real => true
  | .nat, _ => true
  | .int, .rat => true
  | _, _ => t1 == t2

/-- num.ml:66-68 `typ_unop`. -/
def typUnop (_op : UnOp) (t1 t2 : NumTyp) : Bool :=
  t1 == t2 && subNumTyp .int t1

/-- num.ml:70-76 `typ_binop`. -/
def typBinop (op : BinOp) (t1 t2 t3 : NumTyp) : Bool :=
  match op with
  | .add | .mul => t1 == t2 && t1 == t3
  | .sub => t1 == t2 && subNumTyp .int t3
  | .div => t1 == t2 && subNumTyp .rat t3
  | .mod => t1 == t2 && t1 == t3 && subNumTyp t1 .int
  | .pow => t1 == t3 && (t2 == .nat || t2 == .int && subNumTyp .rat t1)
  | _ => false  -- bool ops: unreachable via infer_binop's dispatch

/-- num.ml:79-96 `cvt` (real rows deferred to the Eval layer's
fail-closed check; see header). -/
def cvt (ty : NumTyp) (n : Num) : Option Num :=
  match n, ty with
  | .nat _, .nat => some n
  | .nat v, .int => some (.int v)
  | .nat v, .rat => some (.rat v 1)
  | .int i, .nat => if 0 ≤ i then some (.nat i.toNat) else none
  | .int _, .int => some n
  | .int i, .rat => some (.rat i 1)
  | .rat p q, .nat => if q == 1 && 0 ≤ p then some (.nat p.toNat) else none
  | .rat p q, .int => if q == 1 then some (.int p) else none
  | .rat _ _, .rat => some n
  | _, _ => none  -- real rows: Eval throws first

/-- num.ml:115-120 `abs`. -/
def abs : Num → Num
  | .nat n => .nat n
  | .int i => .int i.natAbs
  | .rat p q => .rat p.natAbs q
  | .real r => .real r  -- unreachable (Eval throws first)

/-- num.ml:122-132 `un`. -/
def un (op : UnOp) (n : Num) : Option Num :=
  match op, n with
  | .plus, .nat v => some (.nat v)
  | .plus, .int _ | .plus, .rat _ _ => some n
  | .minus, .nat v => some (.int (-(Int.ofNat v)))
  | .minus, .int i => some (.int (-i))
  | .minus, .rat p q => some (.rat (-p) q)
  | _, _ => none  -- not/real: unreachable

/-- num.ml:134-174 `bin`. Int mod is `Z.rem` = TRUNCATED (sign of
dividend): Lean `Int.tmod`. Div rows require exact division. -/
def bin (op : BinOp) (n1 n2 : Num) : Option Num :=
  match op, n1, n2 with
  | .add, .nat a, .nat b => some (.nat (a + b))
  | .add, .int a, .int b => some (.int (a + b))
  | .add, .rat p1 q1, .rat p2 q2 =>
    let (p, q) := Rat.add (p1, q1) (p2, q2); some (.rat p q)
  | .sub, .nat a, .nat b => if b ≤ a then some (.nat (a - b)) else none
  | .sub, .int a, .int b => some (.int (a - b))
  | .sub, .rat p1 q1, .rat p2 q2 =>
    let (p, q) := Rat.sub (p1, q1) (p2, q2); some (.rat p q)
  | .mul, .nat a, .nat b => some (.nat (a * b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .mul, .rat p1 q1, .rat p2 q2 =>
    let (p, q) := Rat.mul (p1, q1) (p2, q2); some (.rat p q)
  | .div, .nat a, .nat b =>
    if b != 0 && a % b == 0 then some (.nat (a / b)) else none
  | .div, .int a, .int b =>
    if b != 0 && a.tmod b == 0 then some (.int (a.tdiv b)) else none
  | .div, .rat p1 q1, .rat p2 q2 =>
    if p2 != 0 then
      let (p, q) := Rat.div (p1, q1) (p2, q2); some (.rat p q)
    else none
  | .mod, .nat a, .nat b => if b != 0 then some (.nat (a % b)) else none
  | .mod, .int a, .int b => if b != 0 then some (.int (a.tmod b)) else none
  | .pow, .nat a, .nat b => some (.nat (a ^ b))
  | .pow, .int a, .int b =>
    if 0 ≤ b then some (.int (a ^ b.toNat)) else none
  | .pow, .rat p1 q1, .rat p2 q2 =>
    -- num.ml:165-171: integral non-negative exponent, or reciprocal
    if q2 == 1 && 0 ≤ p2 then
      let k := p2.toNat
      let (p, q) := Rat.mk (p1 ^ k) (q1 ^ k)
      some (.rat p q)
    else if p2 < 0 then
      -- num.ml:167-171 recursive reciprocal case, inlined: the recursive
      -- call has a non-negative integral exponent, so it is exactly the
      -- branch above (recursion depth 1)
      if q2 == 1 then
        let k := (-p2).toNat
        let (p, q) := Rat.mk (p1 ^ k) (q1 ^ k)
        let (p', q') := Rat.div (1, 1) (p, q)
        some (.rat p' q')
      else none
    else none
  | _, _, _ => none

/-- num.ml:176-189 `zero`/`one`/`is_zero`/`is_one` (real: unreachable). -/
def isZero : Num → Bool
  | .nat n => n == 0
  | .int i => i == 0
  | .rat p _ => p == 0
  | .real _ => false

def isOne : Num → Bool
  | .nat n => n == 1
  | .int i => i == 1
  | .rat p q => p == 1 && q == 1
  | .real _ => false

def zero (t : NumTyp) : Num :=
  match t with
  | .nat => .nat 0 | .int => .int 0 | .rat => .rat 0 1 | .real => .real "0"

def one (t : NumTyp) : Num :=
  match t with
  | .nat => .nat 1 | .int => .int 1 | .rat => .rat 1 1 | .real => .real "1"

/-- num.ml:191-195 `is_neg`. -/
def isNeg : Num → Bool
  | .nat _ => false
  | .int i => i < 0
  | .rat p _ => p < 0
  | .real _ => false  -- unreachable

/-- num.ml:232-271 `bin_partial`. OCaml's `when`-guarded rows FALL
THROUGH on guard failure; mirrored as a sequential if-chain in exact
row order (num.ml:257-269). -/
def binPartial (op : BinOp) (arg1 arg2 : α) (of? : α → Option Num)
    (to_ : Num → α) : Option α :=
  match of? arg1, of? arg2 with
  | some n1, some n2 => (bin op n1 n2).map to_
  | o1, o2 =>
    -- neutral elements
    if op == .add && o1.any isZero then some arg2
    else if op == .mul && o1.any isOne then some arg2
    else if (op == .add || op == .sub) && o2.any isZero then some arg1
    else if (op == .mul || op == .div || op == .pow) && o2.any isOne then
      some arg1
    -- absorbing elements
    else if (op == .mul || op == .div || op == .mod || op == .pow)
        && o1.any isZero then some arg1
    else if op == .pow && o1.any isOne then some arg1
    else if op == .mul && o2.any isZero then some arg2
    -- collapsing elements
    else if op == .mod && o2.any isOne then
      o2.map (fun n2 => to_ (zero (toTyp n2)))
    else if op == .pow && o2.any isZero then
      o2.map (fun n2 => to_ (one (toTyp n2)))
    else none

/-- num.ml:273-299 `cmp` (real: unreachable). -/
def cmp (op : CmpOp) (n1 n2 : Num) : Option Bool :=
  match op, n1, n2 with
  | .lt, .nat a, .nat b => some (a < b)
  | .lt, .int a, .int b => some (a < b)
  | .lt, .rat p1 q1, .rat p2 q2 => some (Rat.lt (p1, q1) (p2, q2))
  | .gt, .nat a, .nat b => some (b < a)
  | .gt, .int a, .int b => some (b < a)
  | .gt, .rat p1 q1, .rat p2 q2 => some (Rat.lt (p2, q2) (p1, q1))
  | .le, .nat a, .nat b => some (a ≤ b)
  | .le, .int a, .int b => some (a ≤ b)
  | .le, .rat p1 q1, .rat p2 q2 => some (Rat.le (p1, q1) (p2, q2))
  | .ge, .nat a, .nat b => some (b ≤ a)
  | .ge, .int a, .int b => some (b ≤ a)
  | .ge, .rat p1 q1, .rat p2 q2 => some (Rat.le (p2, q2) (p1, q1))
  | _, _, _ => none

/-- Any real operand? (the Eval layer's fail-closed pre-check) -/
def anyReal : Num → Bool
  | .real _ => true
  | _ => false

end NumOps

/-! ## bool.ml operator semantics -/

namespace BoolOps

/-- bool.ml:25-27 `un`. -/
def un (_op : UnOp) (b : Bool) : Bool := !b

/-- bool.ml:29-34 `bin`. -/
def bin (op : BinOp) (b1 b2 : Bool) : Bool :=
  match op with
  | .and => b1 && b2
  | .or => b1 || b2
  | .impl => !b1 || b2
  | .equiv => b1 == b2
  | _ => false  -- num ops: unreachable via dispatch

/-- bool.ml:36-47 `bin_partial`, row order preserved. -/
def binPartial (op : BinOp) (arg1 arg2 : α) (of? : α → Option Bool)
    (to_ : Bool → α) : Option α :=
  match op, of? arg1, of? arg2 with
  | op, some b1, some b2 => some (to_ (bin op b1 b2))
  | .and, some b1, none => some (if b1 then arg2 else arg1)
  | .and, none, some b2 => some (if b2 then arg1 else arg2)
  | .or, some b1, none => some (if b1 then arg1 else arg2)
  | .or, none, some b2 => some (if b2 then arg2 else arg1)
  | .impl, some b1, none => some (if b1 then arg2 else to_ true)
  | .impl, none, some b2 => if b2 then some arg2 else none
  | .equiv, some b1, none => if b1 then some arg2 else none
  | .equiv, none, some b2 => if b2 then some arg1 else none
  | _, _, _ => none

end BoolOps

/-! ## atom/mixop rendering (atom.ml:111-184, mixop.ml:81-93) -/

namespace XlPrint

open SpecTecLean.Xl

/-- atom.ml:111-184 `to_string` (`Atom "_"` renders as `_`, same as any
other atomid — the special case at atom.ml:113 is identity). -/
def atomToString (a : Atom) : String :=
  match a with
  | .atom s => s
  | .infinity => "infinity"
  | .bot => "_|_"
  | .top => "^|^"
  | .dot => "."
  | .dot2 => ".."
  | .dot3 => "..."
  | .semicolon => ";"
  | .slash => "/"
  | .backslash => "\\"
  | .mem => "<-"
  | .notMem => "</-"
  | .arrow => "->"
  | .arrow2 => "=>"
  | .arrowSub => "->_"
  | .arrow2Sub => "=>_"
  | .colon => ":"
  | .colonSub => ":_"
  | .sub => "<:"
  | .sup => ":>"
  | .assign => ":="
  | .equal => "="
  | .equalSub => "=_"
  | .notEqual => "=/="
  | .less => "<"
  | .greater => ">"
  | .lessEqual => "<="
  | .greaterEqual => ">="
  | .equiv => "=="
  | .equivSub => "==_"
  | .approx => "~~"
  | .approxSub => "~~_"
  | .sqArrow => "~>"
  | .sqArrowSub => "~>_"
  | .sqArrowStar => "~>*"
  | .sqArrowStarSub => "~>*_"
  | .prec => "<<"
  | .succ => ">>"
  | .precSub => "<<_"
  | .succSub => ">>_"
  | .tilesturn => "-|"
  | .turnstile => "|-"
  | .tilesturnSub => "-|_"
  | .turnstileSub => "|-_"
  | .quest => "^?"
  | .star => "^*"
  | .iter => "^+"
  | .plus => "+"
  | .minus => "-"
  | .plusMinus => "+-"
  | .minusPlus => "-+"
  | .times => "*"
  | .not => "~"
  | .and => "/\\"
  | .or => "\\/"
  | .comma => ","
  | .cat => "++"
  | .bar => "|"
  | .bigAnd => "(/\\)"
  | .bigOr => "(\\/)"
  | .bigForall => "(!)"
  | .bigExists => "(?)"
  | .bigAdd => "(+)"
  | .bigMul => "(*)"
  | .bigCat => "(++)"
  | .lParen => "("
  | .lBrack => "["
  | .lBrace => "{"
  | .rParen => ")"
  | .rBrack => "]"
  | .rBrace => "}"

/-- mixop.ml:81-88 `to_string_with` at `f = const "%"`, `s = ""`. -/
def mixopToStringWith (m : Mixop) : String :=
  match m with
  | .arg => "%"
  | .seq ms =>
    String.join (ms.attach.map (fun ⟨m1, _⟩ => mixopToStringWith m1))
  | .atom a => atomToString a
  | .brack l m1 r =>
    atomToString l ++ mixopToStringWith m1 ++ atomToString r
  | .infix m1 a m2 =>
    mixopToStringWith m1 ++ atomToString a ++ mixopToStringWith m2

/-- mixop.ml:90-93 `to_string` (the `Seq (Atom a :: all-Args)` special
case). SEMANTIC: dup-detection and disjointness keys (see header). -/
def mixopToString (m : Mixop) : String :=
  match m with
  | .seq (.atom a :: tail) =>
    if tail.all (fun m1 => match m1 with | .arg => true | _ => false) then
      atomToString a
    else mixopToStringWith m
  | m => mixopToStringWith m

end XlPrint

end SpecTecLean.Il
