/-!
Deep embedding of SpecTec's IL, mirroring `deps/spectec/spectec/src/il/ast.ml`
(spectec @ acc6e834) — specifically the fragment observable through the
`backend-ast` S-expression dump, which is this project's OCaml↔Lean bridge.

Deliberate divergences from ast.ml (mirror doctrine, CLAUDE.md; each also
logged in docs/2026-08-20_arc1-log.md):

- **No source positions.** ast.ml wraps nodes in `phrase` / `note_phrase`
  (util/source.ml) carrying regions and type notes; backend-ast/print.ml
  prints only `.it` and drops both, so the dump carries neither. We embed
  the bare constructors.
- **No hints.** `typfield`/`typcase` hint lists (ast.ml:43-44) are dropped
  by print.ml:89,92; `HintD` (ast.ml:138) prints as `Atom ""` and is
  filtered from scripts (print.ml:220-221,227). Neither is representable
  here; the reader rejects them if ever encountered.
- **Atoms and mixops are opaque dump-level tokens.** ast.ml has structured
  `Atom.atom` / `unit Mixop.mixop`; the dump renders both through
  `Mixop.to_string` (xl/mixop.ml:91-93) / `Atom.to_string`, which is a
  lossy, NON-INJECTIVE flattening (mixop structure and arity are erased;
  e.g. `Seq [Atom a]` and `Seq [Atom a; Arg]` print identically).
  Reconstructing structure would be invention, so `Atom`/`Mixop` here are
  the decoded token strings. Recovering structured mixops needs an
  upstream-side structural dump — recorded as an open question for a later
  arc.
- **`LetPr` has no binder list**: print.ml:166 drops `_qs`.
- **`NumE` reals carry the raw printed token**: OCaml prints `%.17g`
  (print.ml:20), which Lean cannot reproduce bit-for-bit; zero reals occur
  in the wasm-3.0 corpus (grep-verified 2026-08-20).
- **Tuple components get named wrapper types** (`TypBind`, `Dom`) where
  ast.ml uses anonymous products (ast.ml:34,95) — a Lean structural-
  recursion idiom; content is identical.
-/

namespace SpecTecLean.Il

/-- ast.ml:9 `id = string phrase` (region dropped). -/
abbrev Id := String

/-- ast.ml:10 `atom = Atom.atom`, as its dump rendering (see header). -/
abbrev Atom := String

/-- ast.ml:11 `mixop = unit Mixop.mixop`, as its dump rendering. -/
abbrev Mixop := String

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
(print.ml:19); `real` is the raw `%.17g` token (see header). -/
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

/-- ast.ml:43 `typfield` (hints dropped; atom printed as mixop token,
print.ml:90). -/
inductive TypField where
  | mk (atom : Atom) (t : Typ) (quants : List Param) (prems : List Prem)

/-- ast.ml:44 `typcase` (hints dropped). -/
inductive TypCase where
  | mk (op : Mixop) (t : Typ) (quants : List Param) (prems : List Prem)

/-- ast.ml:54-84 `exp'`. Constructor order follows ast.ml. -/
inductive Exp where
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

/-- ast.ml:86 `expfield` (atom printed as mixop token, print.ml:131-132). -/
inductive ExpField where
  | mk (atom : Atom) (e : Exp)

/-- ast.ml:89-93 `path'`. -/
inductive Path where
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

/-- ast.ml:157-163 `prem'` (LetPr binders dropped, see header). -/
inductive Prem where
  | rulePr (x : Id) (args : List Arg) (op : Mixop) (e : Exp)  -- RulePr
  | ifPr (e : Exp)                           -- IfPr
  | letPr (e1 e2 : Exp)                      -- LetPr
  | elsePr                                   -- ElsePr
  | iterPr (pr : Prem) (ie : IterExp)        -- IterPr
  | negPr (pr : Prem)                        -- NegPr

end

deriving instance Repr for Iter, Typ, TypBind, DefTyp, TypField, TypCase,
  Exp, ExpField, Path, IterExp, Dom, Sym, Arg, Param, Prem
deriving instance BEq for Iter, Typ, TypBind, DefTyp, TypField, TypCase,
  Exp, ExpField, Path, IterExp, Dom, Sym, Arg, Param, Prem

/-- ast.ml:129 `quant = param`. -/
abbrev Quant := Param

/-- ast.ml:141-142 `inst'`. -/
inductive Inst where
  | mk (quants : List Quant) (args : List Arg) (dt : DefTyp)
deriving Repr, BEq

/-- ast.ml:145-146 `rule'`. -/
inductive Rule where
  | mk (x : Id) (quants : List Quant) (op : Mixop) (e : Exp)
       (prems : List Prem)
deriving Repr, BEq

/-- ast.ml:149-150 `clause'`. -/
inductive Clause where
  | mk (quants : List Quant) (args : List Arg) (e : Exp) (prems : List Prem)
deriving Repr, BEq

/-- ast.ml:153-154 `prod'`. -/
inductive Prod where
  | mk (quants : List Quant) (g : Sym) (e : Exp) (prems : List Prem)
deriving Repr, BEq

/-- ast.ml:132-138 `def'` (HintD absent from dumps, see header). -/
inductive Def where
  | typD (x : Id) (params : List Param) (insts : List Inst)         -- TypD
  | relD (x : Id) (params : List Param) (op : Mixop) (t : Typ)
         (rules : List Rule)                                        -- RelD
  | decD (x : Id) (params : List Param) (t : Typ)
         (clauses : List Clause)                                    -- DecD
  | gramD (x : Id) (params : List Param) (t : Typ)
          (prods : List Prod)                                       -- GramD
  | recD (ds : List Def)                                            -- RecD
deriving Repr, BEq

/-- ast.ml:178 `script = def list`. -/
abbrev Script := List Def

end SpecTecLean.Il
