/-!
Structured atoms and mixops, mirroring `deps/spectec/spectec/src/xl/atom.ml`
and `xl/mixop.ml` (spectec @ acc6e834 + vendored patch
`patches/0001-structured-ast-dump.patch`, which dumps them losslessly in
`--ast-structured` mode — objective decision D3).

Encoding (patched print.ml `atom_sx`/`mixop_sx`):
  Atom.Atom s           → (a "<escaped s>")
  fixed constructor C   → (s <Atom.name C>)     [70 names, verified unique]
  Mixop.Arg _           → %                     [bare atom; `unit mixop`]
  Mixop.Atom at         → <atom>
  Mixop.Brack (l,m,r)   → (brack <atom> <mixop> <atom>)
  Mixop.Infix (m1,a,m2) → (infix <mixop> <atom> <mixop>)
  Mixop.Seq ms          → (seq <mixop>*)

Divergences: atom.ml wraps `atom'` in a `note_phrase` carrying a region
and mutable latex `info` (atom.ml:3-7) — neither is dumped (info is a
latex-backend device; `Atom.eq`/`compare` use `.it` only, atom.ml:79-83),
so `Atom` here is bare `atom'`. `Mixop.Arg`'s payload is `unit` in IL
(il/ast.ml:11 `unit Mixop.mixop`), so `arg` carries nothing.
-/

namespace SpecTecLean.Xl

/-- xl/atom.ml:8-76 `atom'`, constructor order preserved. -/
inductive Atom where
  | atom (s : String)   -- Atom of string (atomid)
  | infinity | bot | top
  | dot | dot2 | dot3 | semicolon | slash | backslash
  | not | and | or
  | mem | notMem
  | arrow | arrow2 | arrowSub | arrow2Sub
  | colon | colonSub | sub | sup | assign
  | equal | equalSub | notEqual
  | less | greater | lessEqual | greaterEqual
  | equiv | equivSub | approx | approxSub
  | sqArrow | sqArrowSub | sqArrowStar | sqArrowStarSub
  | prec | succ | precSub | succSub
  | turnstile | turnstileSub | tilesturn | tilesturnSub
  | quest | star | iter
  | plus | minus | plusMinus | minusPlus | times
  | comma | cat | bar
  | bigAnd | bigOr | bigForall | bigExists | bigAdd | bigMul | bigCat
  | lParen | rParen | lBrack | rBrack | lBrace | rBrace
deriving Repr, BEq, Inhabited

namespace Atom

/-- xl/atom.ml:190-262 `name` for the fixed constructors (the `Atom s`
case is encoded as `(a "s")`, not by name). All 70 names verified
pairwise distinct at the pin (2026-08-20). -/
def fixedName : Atom → Option String
  | .atom _ => none
  | .infinity => some "infty"
  | .bot => some "bot"
  | .top => some "top"
  | .dot => some "dot"
  | .dot2 => some "dotdot"
  | .dot3 => some "dots"
  | .semicolon => some "semicolon"
  | .slash => some "slash"
  | .backslash => some "setminus"
  | .not => some "not"
  | .and => some "and"
  | .or => some "or"
  | .mem => some "in"
  | .notMem => some "notin"
  | .arrow => some "arrow"
  | .arrow2 => some "darrow"
  | .arrowSub => some "arrow_"
  | .arrow2Sub => some "darrow_"
  | .colon => some "colon"
  | .colonSub => some "colon_"
  | .sub => some "sub"
  | .sup => some "sup"
  | .assign => some "assign"
  | .equal => some "eq"
  | .equalSub => some "eq_"
  | .notEqual => some "neq"
  | .less => some "lt"
  | .greater => some "gt"
  | .lessEqual => some "leq"
  | .greaterEqual => some "geq"
  | .equiv => some "equiv"
  | .equivSub => some "equiv_"
  | .approx => some "approx"
  | .approxSub => some "approx_"
  | .sqArrow => some "sqarrow"
  | .sqArrowSub => some "sqarrow_"
  | .sqArrowStar => some "sqarrowstar"
  | .sqArrowStarSub => some "sqarrowstar_"
  | .prec => some "prec"
  | .succ => some "succ"
  | .precSub => some "prec_"
  | .succSub => some "succ_"
  | .turnstile => some "vdash"
  | .turnstileSub => some "vdash_"
  | .tilesturn => some "dashv"
  | .tilesturnSub => some "dashv_"
  | .quest => some "quest"
  | .star => some "ast"
  | .iter => some "iter"
  | .plus => some "plus"
  | .minus => some "minus"
  | .plusMinus => some "plusminus"
  | .minusPlus => some "minusplus"
  | .times => some "times"
  | .comma => some "comma"
  | .cat => some "cat"
  | .bar => some "bar"
  | .bigAnd => some "bigand"
  | .bigOr => some "bigor"
  | .bigForall => some "forall"
  | .bigExists => some "exists"
  | .bigAdd => some "bigadd"
  | .bigMul => some "bigmul"
  | .bigCat => some "bigcat"
  | .lParen => some "lparen"
  | .rParen => some "rparen"
  | .lBrack => some "lbrack"
  | .rBrack => some "rbrack"
  | .lBrace => some "lbrace"
  | .rBrace => some "rbrace"

/-- Inverse of `fixedName` (fail-closed: unknown name → none). -/
def ofFixedName (s : String) : Option Atom :=
  fixedAtoms.find? (fun a => a.fixedName == some s)
where
  fixedAtoms : List Atom :=
    [.infinity, .bot, .top, .dot, .dot2, .dot3, .semicolon, .slash,
     .backslash, .not, .and, .or, .mem, .notMem, .arrow, .arrow2,
     .arrowSub, .arrow2Sub, .colon, .colonSub, .sub, .sup, .assign,
     .equal, .equalSub, .notEqual, .less, .greater, .lessEqual,
     .greaterEqual, .equiv, .equivSub, .approx, .approxSub, .sqArrow,
     .sqArrowSub, .sqArrowStar, .sqArrowStarSub, .prec, .succ, .precSub,
     .succSub, .turnstile, .turnstileSub, .tilesturn, .tilesturnSub,
     .quest, .star, .iter, .plus, .minus, .plusMinus, .minusPlus, .times,
     .comma, .cat, .bar, .bigAnd, .bigOr, .bigForall, .bigExists,
     .bigAdd, .bigMul, .bigCat, .lParen, .rParen, .lBrack, .rBrack,
     .lBrace, .rBrace]

end Atom

/-- xl/mixop.ml:5-10 `'a mixop` at `'a = unit` (il/ast.ml:11). -/
inductive Mixop where
  | arg                                      -- Arg of 'a (unit)
  | atom (a : Atom)                          -- Atom
  | brack (l : Atom) (m : Mixop) (r : Atom)  -- Brack
  | infix (m1 : Mixop) (a : Atom) (m2 : Mixop) -- Infix
  | seq (ms : List Mixop)                    -- Seq
deriving Repr, BEq, Inhabited

end SpecTecLean.Xl
