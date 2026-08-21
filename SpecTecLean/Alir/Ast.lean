import SpecTecLean.Il.Ast
/-!
AL (algorithmic language) AST — mirror of
`deps/spectec/spectec/src/al/ast.ml` (156 lines; spectec @ acc6e834 +
vendored patches). Arc-3b stage 1.

Mirror notes (each a deliberate, documented representation divergence;
semantics preserved):
- `'a growable_array = 'a array ref` (ast.ml:27) → `List Value`: Lean
  has no in-place mutation; all upstream uses are read/copy/append,
  mirrored functionally in the interpreter.
- `('a, 'b) record = ('a * 'b ref) list` (ast.ml:29) → assoc `List`
  without the ref cell (same reason).
- Source regions and the `int` instruction note (coverage index,
  ast.ml:118 `(instr', int) note_phrase`) are dropped: no `at` tracking
  in the Lean mirror yet; the instruction note is only used by
  upstream's coverage counter (interpreter.ml:580). Expressions keep
  their `Il.Typ` note (ast.ml:60 `(expr', Il.Ast.typ) note_phrase`)
  because `AppendI` and assignment consult it.
- `typ = Il.Ast.typ` (ast.ml:13) → `SpecTecLean.Il.Typ`; atoms/mixops
  are the shared Xl mirrors, as upstream shares Xl (ast.ml:5-6).
- `unop`/`binop` are OCaml polymorphic-variant UNIONS
  (ast.ml:48-49: `[Bool.unop | Num.unop]`,
  `[Bool.binop | Num.binop | Bool.cmpop | Num.cmpop]`); Lean mirrors
  them as single inductives covering the same constructor sets
  (Il.UnOp / Il.BinOp+Il.CmpOp carry the identical cases, but AL merges
  binop and cmpop into one syntactic class, so Alir declares its own).
-/

namespace SpecTecLean.Il.Alir

open SpecTecLean.Il

/-- ast.ml:17 `id = string`. -/
abbrev AlId := String
/-- ast.ml:21 `anchor = string`. -/
abbrev Anchor := String

/-- ast.ml:33-43 `value`. `FnameV` = first-order function name. -/
inductive Value where
  | numV (n : Num)
  | boolV (b : Bool)
  | textV (t : String)
  | listV (vs : List Value)
  | strV (fields : List (AlId × Value))
  | caseV (tag : AlId) (args : List Value)
  | optV (v? : Option Value)
  | tupV (vs : List Value)
  | fnameV (f : AlId)
deriving Repr, BEq, Inhabited

/-- ast.ml:45-47 `extend_dir`. -/
inductive ExtendDir where
  | front
  | back
deriving Repr, BEq, Inhabited

/-- ast.ml:48 `unop = [Bool.unop | Num.unop]`. -/
inductive UnOp where
  | not | plus | minus
deriving Repr, BEq, Inhabited

/-- ast.ml:49 `binop = [Bool.binop | Num.binop | Bool.cmpop | Num.cmpop]`
— AL merges IL's binop and cmpop into one class. -/
inductive BinOp where
  | and | or | impl | equiv
  | add | sub | mul | div | mod | pow
  | eq | ne | lt | gt | le | ge
deriving Repr, BEq, Inhabited

mutual
/-- ast.ml:54-58 `iter` (AL keeps ListN's exp + optional index id). -/
inductive Iter where
  | opt
  | list
  | list1
  | listN (e : Expr) (x? : Option AlId)

/-- ast.ml:60 `expr = (expr', Il.Ast.typ) note_phrase`. -/
inductive Expr where
  | mk (it : Expr') (note : Typ)

/-- ast.ml:61-103 `expr'`. Constructor order and payload shapes follow
the source; conditions/assertion forms included for completeness even
where the stage-1 interpreter rejects them (fail-closed). -/
inductive Expr' where
  | varE (x : AlId)
  | numE (n : Num)
  | boolE (b : Bool)
  | cvtE (e : Expr) (nt1 nt2 : NumTyp)
  | unE (op : UnOp) (e : Expr)
  | binE (op : BinOp) (e1 e2 : Expr)
  | accE (e : Expr) (p : Path)
  | updE (e1 : Expr) (ps : List Path) (e2 : Expr)
  | extE (e1 : Expr) (ps : List Path) (e2 : Expr) (dir : ExtendDir)
  | strE (fields : List (Atom × Expr))
  | compE (e1 e2 : Expr)
  | catE (e1 e2 : Expr)
  | memE (e1 e2 : Expr)
  | lenE (e : Expr)
  | tupE (es : List Expr)
  | caseE (op : Mixop) (es : List Expr)
  | callE (f : AlId) (args : List Arg)
  | invCallE (f : AlId) (idxs : List (Option Nat)) (args : List Arg)
  | iterE (e : Expr) (ie : IterExp)
  | optE (e? : Option Expr)
  | listE (es : List Expr)
  | liftE (e : Expr)
  | getCurStateE
  | getCurContextE (a : Atom)
  | chooseE (e : Expr)
  | isCaseOfE (e : Expr) (a : Atom)
  | isValidE (e : Expr)
  | contextKindE (a : Atom)
  | isDefinedE (e : Expr)
  | matchE (e1 e2 : Expr)
  | hasTypeE (e : Expr) (t : Typ)
  | topValueE (e? : Option Expr)
  | topValuesE (e : Expr)
  | subE (x : AlId) (t : Typ)
  | relE (x : AlId) (es : List Expr)
  | yetE (s : String)

/-- ast.ml:105-109 `path'` (regions dropped, header note). -/
inductive Path where
  | idxP (e : Expr)
  | sliceP (e1 e2 : Expr)
  | dotP (a : Atom)

/-- ast.ml:111-115 `arg'`. -/
inductive Arg where
  | expA (e : Expr)
  | typA (t : Typ)
  | defA (x : AlId)

/-- ast.ml:117 `iterexp = iter * (id * expr) list`. -/
inductive IterExp where
  | mk (iter : Iter) (xes : List (AlId × Expr))
end

/-- ast.ml:120-146 `instr'` (int note dropped, header note). -/
inductive Instr where
  | ifI (cond : Expr) (thn els : List Instr)
  | eitherI (il1 il2 : List Instr)
  | enterI (e1 e2 : Expr) (il : List Instr)
  | assertI (cond : Expr)
  | pushI (e : Expr)
  | popI (e : Expr)
  | popAllI (e : Expr)
  | letI (lhs rhs : Expr)
  | trapI
  | failI
  | throwI (e : Expr)
  | nopI
  | returnI (e? : Option Expr)
  | executeI (e : Expr)
  | executeSeqI (e : Expr)
  | performI (f : AlId) (args : List Arg)
  | exitI (a : Atom)
  | replaceI (e1 : Expr) (p : Path) (e2 : Expr)
  | appendI (e1 e2 : Expr)
  | forEachI (xes : List (AlId × Expr)) (il : List Instr)
  | otherwiseI (il : List Instr)
  | yetI (s : String)

/-- ast.ml:148-153 `algorithm'`. -/
inductive Algorithm where
  | ruleA (op : Mixop) (anchor : Anchor) (args : List Arg)
      (body : List Instr)
  | funcA (f : AlId) (args : List Arg) (body : List Instr)

instance : Inhabited Expr := ⟨.mk (.boolE false) .boolT⟩

namespace Expr
def it : Expr → Expr' | .mk it _ => it
def note : Expr → Typ | .mk _ n => n
end Expr

end SpecTecLean.Il.Alir
