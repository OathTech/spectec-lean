import SpecTecLean.Xl
/-!
Deep embedding of SpecTec's IL, mirroring `deps/spectec/spectec/src/il/ast.ml`
(spectec @ acc6e834 + vendored patch `patches/0001-structured-ast-dump.patch`)
— the fragment observable through the `--ast-structured` dump, this
project's OCaml↔Lean bridge (objective decision D3 made it lossless for
atoms/mixops, LetPr binders, and definition-level regions).

Deliberate divergences from ast.ml (mirror doctrine, CLAUDE.md; each also
logged in the arc logs):

- **Positions at definition granularity only.** ast.ml wraps every node in
  `phrase`/`note_phrase` (util/source.ml) with regions and type notes; the
  patched dump carries regions for `def`/`inst`/`rule`/`clause`/`prod`
  nodes only (`at?` fields below). Expression-level positions and type
  notes remain undumped — extend the patch when an arc needs them.
- **No hints.** `typfield`/`typcase` hint lists (ast.ml:43-44) are dropped
  by print.ml:89,92; `HintD` (ast.ml:138) prints as `Atom ""` and is
  filtered from scripts (print.ml:220-221,227). Neither is representable
  here; the reader rejects them if ever encountered.
- **Atoms and mixops are STRUCTURED** (`SpecTecLean.Xl`), mirroring
  xl/atom.ml + xl/mixop.ml via the D3 patch's lossless encoding. (Arc-1
  carried them as lossy `Mixop.to_string` tokens; superseded 2026-08-20.)
- **`NumE` reals fail closed at the reader**: OCaml prints `%.17g`
  (print.ml:20), which Lean cannot reproduce bit-for-bit; zero reals occur
  in any corpus (audit 2026-08-20). The `Num.real` constructor remains for
  printer-mirror completeness.
- **Tuple components get named wrapper types** (`TypBind`, `Dom`) where
  ast.ml uses anonymous products (ast.ml:34,95) — a Lean structural-
  recursion idiom; content is identical.
- **`projE`'s index and `numG`'s value are `Nat`** where ast.ml:63,103
  have OCaml `int`: both are non-negative throughout upstream
  (frontend/elab.ml builds `NumG` from `Num.nat`; proj indices are tuple
  positions), and the reader enforces the OCaml `max_int` bound
  (audit 2026-08-20, findings A3/A4/B9).
-/

namespace SpecTecLean.Il

/-- ast.ml:9 `id = string phrase` (region dropped). -/
abbrev Id := String

/-- ast.ml:10 `atom = Atom.atom`, structured (Xl.Atom; D3). -/
abbrev Atom := SpecTecLean.Xl.Atom

/-- ast.ml:11 `mixop = unit Mixop.mixop`, structured (Xl.Mixop; D3). -/
abbrev Mixop := SpecTecLean.Xl.Mixop

/-- util/source.ml:3-4 `pos`/`region`, as dumped by the patch's
`(at "file" l1 c1 l2 c2)` nodes. Lines/columns are OCaml ints (line -1
occurs for binary-offset positions upstream), hence `Int`. -/
structure Region where
  file : String
  l1 : Int
  c1 : Int
  l2 : Int
  c2 : Int
deriving Repr, BEq, Inhabited

/-- xl/num.ml:14 `typ = [`NatT | `IntT | `RatT | `RealT]`. -/
inductive NumTyp where
  | nat | int | rat | real
deriving Repr, BEq, Inhabited

/-- ast.ml:26 `optyp = [Bool.typ | Num.typ]` (xl/bool.ml:1 `[`BoolT]`). -/
inductive OpTyp where
  | bool
  | num (nt : NumTyp)
deriving Repr, BEq, Inhabited

/-- xl/num.ml:6-12 `num`. `rat` is zarith `Q.t` as printed `num/den`
(print.ml:19; reader enforces Q.t canonicity); `real` is the raw `%.17g`
token (reader rejects; see header). -/
inductive Num where
  | nat (n : Nat)
  | int (i : Int)
  | rat (num den : Int)
  | real (raw : String)
deriving Repr, BEq, Inhabited

/-- ast.ml:49 `unop = [Bool.unop | Num.unop]`
(xl/bool.ml:3 `[`NotOp]`, xl/num.ml:16 `[`PlusOp | `MinusOp]`).
print.ml:25-30 also matches `PlusMinusOp`/`MinusPlusOp`, unreachable from
this type (open polymorphic variants) — not mirrored. -/
inductive UnOp where
  | not | plus | minus
deriving Repr, BEq, Inhabited

/-- ast.ml:50 `binop` (xl/bool.ml:4, xl/num.ml:17). -/
inductive BinOp where
  | and | or | impl | equiv
  | add | sub | mul | div | mod | pow
deriving Repr, BEq, Inhabited

/-- ast.ml:51 `cmpop` (xl/bool.ml:5, xl/num.ml:18). -/
inductive CmpOp where
  | eq | ne | lt | gt | le | ge
deriving Repr, BEq, Inhabited

mutual

/-- ast.ml:16-20 `iter`. -/
inductive Iter where
  | opt
  | list
  | list1
  | listN (e : Exp) (x : Option Id)

/-- ast.ml:29-35 `typ'`. -/
inductive Typ where
  | varT (x : Id) (args : List Arg)          -- VarT
  | boolT                                    -- BoolT
  | numT (nt : NumTyp)                       -- NumT
  | textT                                    -- TextT
  | tupT (binds : List TypBind)              -- TupT
  | iterT (t : Typ) (it : Iter)              -- IterT

/-- ast.ml:34 `(id * typ)` in TupT, printed as `(bind id typ)`
(print.ml:86-87). -/
inductive TypBind where
  | mk (x : Id) (t : Typ)

/-- ast.ml:38-41 `deftyp'`. -/
inductive DefTyp where
  | aliasT (t : Typ)                         -- AliasT
  | structT (fields : List TypField)         -- StructT
  | variantT (cases : List TypCase)          -- VariantT

/-- ast.ml:43 `typfield` (hints dropped; atom now structural, patched
print.ml `atom`). -/
inductive TypField where
  | mk (atom : Atom) (t : Typ) (quants : List Param) (prems : List Prem)

/-- ast.ml:44 `typcase` (hints dropped). -/
inductive TypCase where
  | mk (op : Mixop) (t : Typ) (quants : List Param) (prems : List Prem)

/-- ast.ml:53 `exp = (exp', typ) note_phrase`: every expression carries
its TYPE annotation (`note`), dumped by patch D3b as `(! <it> <note>)` —
the semantic layer consumes notes (subst.ml:195, eval.ml ×17, valid.ml).
Region still dropped (expression positions undumped). -/
inductive Exp where
  | mk (it : Exp') (note : Typ)

/-- ast.ml:54-84 `exp'`. Constructor order follows ast.ml. -/
inductive Exp' where
  | varE (x : Id)                            -- VarE
  | boolE (b : Bool)                         -- BoolE
  | numE (n : Num)                           -- NumE
  | textE (t : String)                       -- TextE
  | unE (op : UnOp) (t : OpTyp) (e : Exp)    -- UnE
  | binE (op : BinOp) (t : OpTyp) (e1 e2 : Exp)   -- BinE
  | cmpE (op : CmpOp) (t : OpTyp) (e1 e2 : Exp)   -- CmpE
  | tupE (es : List Exp)                     -- TupE
  | projE (e : Exp) (i : Nat)                -- ProjE
  | caseE (op : Mixop) (e : Exp)             -- CaseE
  | uncaseE (e : Exp) (op : Mixop)           -- UncaseE
  | optE (e? : Option Exp)                   -- OptE
  | theE (e : Exp)                           -- TheE
  | strE (fields : List ExpField)            -- StrE
  | dotE (e : Exp) (atom : Atom)             -- DotE
  | compE (e1 e2 : Exp)                      -- CompE
  | listE (es : List Exp)                    -- ListE
  | liftE (e : Exp)                          -- LiftE
  | memE (e1 e2 : Exp)                       -- MemE
  | lenE (e : Exp)                           -- LenE
  | catE (e1 e2 : Exp)                       -- CatE
  | idxE (e1 e2 : Exp)                       -- IdxE
  | sliceE (e1 e2 e3 : Exp)                  -- SliceE
  | updE (e1 : Exp) (p : Path) (e2 : Exp)    -- UpdE
  | extE (e1 : Exp) (p : Path) (e2 : Exp)    -- ExtE
  | ifE (e1 e2 e3 : Exp)                     -- IfE
  | callE (x : Id) (args : List Arg)         -- CallE
  | iterE (e : Exp) (ie : IterExp)           -- IterE
  | cvtE (e : Exp) (nt1 nt2 : NumTyp)        -- CvtE
  | subE (e : Exp) (t1 t2 : Typ)             -- SubE

/-- ast.ml:86 `expfield` (atom structural, patched print.ml). -/
inductive ExpField where
  | mk (atom : Atom) (e : Exp)

/-- ast.ml:88 `path = (path', typ) note_phrase` (patch D3b `(! …)`). -/
inductive Path where
  | mk (it : Path') (note : Typ)

/-- ast.ml:89-93 `path'`. -/
inductive Path' where
  | rootP                                    -- RootP
  | idxP (p : Path) (e : Exp)                -- IdxP
  | sliceP (p : Path) (e1 e2 : Exp)          -- SliceP
  | dotP (p : Path) (atom : Atom)            -- DotP

/-- ast.ml:95 `iterexp = iter * (id * exp) list`. -/
inductive IterExp where
  | mk (it : Iter) (doms : List Dom)

/-- ast.ml:95 `(id * exp)`, printed as `(dom id exp)` (print.ml:142). -/
inductive Dom where
  | mk (x : Id) (e : Exp)

/-- ast.ml:101-110 `sym'`. -/
inductive Sym where
  | varG (x : Id) (args : List Arg)          -- VarG
  | numG (n : Nat)                           -- NumG (int, printed 0x%02X)
  | textG (t : String)                       -- TextG
  | epsG                                     -- EpsG
  | seqG (gs : List Sym)                     -- SeqG
  | altG (gs : List Sym)                     -- AltG
  | rangeG (g1 g2 : Sym)                     -- RangeG
  | iterG (g : Sym) (ie : IterExp)           -- IterG
  | attrG (e : Exp) (g : Sym)                -- AttrG

/-- ast.ml:116-120 `arg'`. -/
inductive Arg where
  | expA (e : Exp)                           -- ExpA
  | typA (t : Typ)                           -- TypA
  | defA (x : Id)                            -- DefA
  | gramA (g : Sym)                          -- GramA

/-- ast.ml:123-127 `param'`. -/
inductive Param where
  | expP (x : Id) (t : Typ)                  -- ExpP
  | typP (x : Id)                            -- TypP
  | defP (x : Id) (params : List Param) (t : Typ)   -- DefP
  | gramP (x : Id) (params : List Param) (t : Typ)  -- GramP

/-- ast.ml:157-163 `prem'` (LetPr binders now carried — D3 patch dumps
`(let param* e1 e2)`, superseding the arc-1 dropped-binders divergence). -/
inductive Prem where
  | rulePr (x : Id) (args : List Arg) (op : Mixop) (e : Exp)  -- RulePr
  | ifPr (e : Exp)                           -- IfPr
  | letPr (quants : List Param) (e1 e2 : Exp)  -- LetPr
  | elsePr                                   -- ElsePr
  | iterPr (pr : Prem) (ie : IterExp)        -- IterPr
  | negPr (pr : Prem)                        -- NegPr

end

deriving instance Repr for Iter, Typ, TypBind, DefTyp, TypField, TypCase,
  Exp, Exp', ExpField, Path, Path', IterExp, Dom, Sym, Arg, Param, Prem
deriving instance BEq for Iter, Typ, TypBind, DefTyp, TypField, TypCase,
  Exp, Exp', ExpField, Path, Path', IterExp, Dom, Sym, Arg, Param, Prem

/-- Accessors mirroring `phrase` projections (`.it` / `.note`). -/
def Exp.it : Exp → Exp' | .mk it _ => it
def Exp.note : Exp → Typ | .mk _ note => note
def Path.it : Path → Path' | .mk it _ => it
def Path.note : Path → Typ | .mk _ note => note

/-- ast.ml:129 `quant = param`. -/
abbrev Quant := Param

/-- ast.ml:141-142 `inst'` (+ dumped region, D3). -/
inductive Inst where
  | mk (at? : Option Region) (quants : List Quant) (args : List Arg)
       (dt : DefTyp)
deriving Repr, BEq

/-- ast.ml:145-146 `rule'` (+ dumped region, D3). -/
inductive Rule where
  | mk (x : Id) (at? : Option Region) (quants : List Quant) (op : Mixop)
       (e : Exp) (prems : List Prem)
deriving Repr, BEq

/-- ast.ml:149-150 `clause'` (+ dumped region, D3). -/
inductive Clause where
  | mk (at? : Option Region) (quants : List Quant) (args : List Arg)
       (e : Exp) (prems : List Prem)
deriving Repr, BEq

/-- ast.ml:153-154 `prod'` (+ dumped region, D3). -/
inductive Prod where
  | mk (at? : Option Region) (quants : List Quant) (g : Sym) (e : Exp)
       (prems : List Prem)
deriving Repr, BEq

/-- ast.ml:132-138 `def'` (+ dumped regions, D3; HintD absent from
dumps, see header). -/
inductive Def where
  | typD (x : Id) (at? : Option Region) (params : List Param)
         (insts : List Inst)                                        -- TypD
  | relD (x : Id) (at? : Option Region) (params : List Param)
         (op : Mixop) (t : Typ) (rules : List Rule)                 -- RelD
  | decD (x : Id) (at? : Option Region) (params : List Param)
         (t : Typ) (clauses : List Clause)                          -- DecD
  | gramD (x : Id) (at? : Option Region) (params : List Param)
          (t : Typ) (prods : List Prod)                             -- GramD
  | recD (at? : Option Region) (ds : List Def)                      -- RecD
deriving Repr, BEq

/-- ast.ml:178 `script = def list`. -/
abbrev Script := List Def

end SpecTecLean.Il
