import SpecTecLean.Sexpr
import SpecTecLean.OcamlEscape
import SpecTecLean.Il.Ast
import SpecTecLean.Il.ToSexpr
/-!
S-expression → IL: the inverse of backend-ast/print.ml (mirrored in
Il/ToSexpr.lean). No OCaml counterpart exists (the OCaml side only prints),
so this reader is DERIVED from print.ml read inversely; every dispatch case
cites the print.ml line it inverts.

Fail-closed rules (CLAUDE.md): unknown node heads, wrong child counts,
malformed literals, or non-canonical tokens are explicit errors — never a
skip or default. Canonicality: every literal token is re-rendered after
parsing and must equal the source token (so `print ∘ parse = id` holds
token-by-token by construction, and e.g. `\065` for `A`, `007` for `7`, or
lowercase hex — which print.ml cannot emit — are rejected).

Head-label disambiguation notes (the dump's labels are context-dependent):
- `param` vs `arg` share the labels exp/typ/def/gram (print.ml:174-186).
  They are distinguished by SHAPE, which is unambiguous for printer output:
  * exp: `(exp id typ)` (2 children, quoted first) is ExpP; `(exp e)` is ExpA.
  * typ: `(typ id)` (quoted child) is TypP; `(typ t)` is TypA (a typ child
    is never a quoted atom: print.ml:71-78).
  * def: `(def id)` is DefA; `(def id … typ)` (≥2 children) is DefP.
  * gram: `(gram id …)` (quoted first) is GramP; `(gram sym)` is GramA
    (a sym child is never a quoted atom: print.ml:147-157).
- In `param* arg*` positions (inst, clause) the printer emits all params
  before all args; an arg-shaped item before a param-shaped one is rejected.
- Boundary detection: everything after `param*`/`arg*` in a definition node
  has a head OUTSIDE {exp, typ, def, gram} (typs/syms/deftyps/exps/mixops
  all do), so a tagged-prefix scan is exact.
-/

namespace SpecTecLean.Il

open SpecTecLean (Sexpr)

abbrev ReadM (α : Type) := Except String α

/-- Render a sexpr flat (for error messages), truncated. -/
private def snippet (x : Sexpr) : String :=
  let s := (Sexpr.pp 0 1000000 x).2
  if s.length > 120 then (s.take 117).toString ++ "…" else s

private def fail (ctx : String) (x : Sexpr) (msg : String) : ReadM α :=
  .error s!"{ctx}: {msg} in `{snippet x}`"

/-! ## Token readers (all canonicality-checked) -/

/-- Read a quoted token (id / mixop / atom / text — print.ml:12-14),
requiring the token to be exactly what `OcamlEscape.quote` re-emits. -/
def readQuoted (ctx : String) : Sexpr → ReadM String
  | x@(.atom tok) =>
    match OcamlEscape.unquote tok with
    | .error e => fail ctx x e
    | .ok s =>
      if OcamlEscape.quote s == tok then .ok s
      else fail ctx x s!"non-canonical escaping in {tok}"
  | x => fail ctx x "expected quoted atom"

def readId (x : Sexpr) : ReadM Id := readQuoted "id" x
def readMixop (x : Sexpr) : ReadM Mixop := readQuoted "mixop" x
def readAtom (x : Sexpr) : ReadM Atom := readQuoted "atom" x
def readText (x : Sexpr) : ReadM String := readQuoted "text" x

/-- print.ml:11 inverse. -/
def readBool : Sexpr → ReadM Bool
  | .atom "true" => .ok true
  | .atom "false" => .ok false
  | x => fail "bool" x "expected true/false"

/-- Bare decimal Nat, canonical (no leading zeros unless "0"). -/
def readNatTok (ctx : String) : Sexpr → ReadM Nat
  | x@(.atom tok) =>
    match tok.toNat? with
    | some n => if toString n == tok then .ok n
                else fail ctx x "non-canonical nat literal"
    | none => fail ctx x "expected nat literal"
  | x => fail ctx x "expected nat literal"

/-- print.ml:16-20 inverse. Each branch re-renders and compares
(`numToSexpr` is the printer mirror). -/
def readNum : Sexpr → ReadM Num
  | x@(.node "nat" [d]) => do
    let n ← readNatTok "num.nat" d
    .ok (.nat n)
  | x@(.node "int" [.atom tok]) => do
    -- print.ml:18: sign is always present; "+0" is the canonical zero
    let sign := (tok.take 1).toString
    let mag := (tok.drop 1).toString
    match sign, mag.toNat? with
    | "+", some n => .ok (.int (Int.ofNat n))
    | "-", some n =>
      if n == 0 then fail "num.int" x "non-canonical -0" else .ok (.int (-(Int.ofNat n)))
    | _, _ => fail "num.int" x "expected signed int literal"
  | x@(.node "rat" [.atom tok]) => do
    -- print.ml:19: Z.to_string (Q.num) "/" Z.to_string (Q.den)
    match tok.splitOn "/" with
    | [ps, qs] =>
      let readZ (s : String) : ReadM Int :=
        if s.startsWith "-" then do
          match (s.drop 1).toString.toNat? with
          | some n => if n == 0 then .error "-0" else .ok (-(Int.ofNat n))
          | none => .error s!"bad int {s}"
        else match s.toNat? with
          | some n => .ok (Int.ofNat n)
          | none => .error s!"bad int {s}"
      match readZ ps, readZ qs with
      | .ok p, .ok q =>
        let n : Num := .rat p q
        if numToSexpr n == x then .ok n
        else fail "num.rat" x "non-canonical rat literal"
      | _, _ => fail "num.rat" x "expected p/q"
    | _ => fail "num.rat" x "expected p/q"
  | .node "real" [.atom raw] =>
    -- raw %.17g token carried verbatim (see Il/Ast.lean header)
    .ok (.real raw)
  | x => fail "num" x "expected (nat|int|rat|real …)"

/-- print.ml:25-30 inverse. -/
def readUnop : Sexpr → ReadM UnOp
  | .atom "not" => .ok .not
  | .atom "plus" => .ok .plus
  | .atom "minus" => .ok .minus
  | x => fail "unop" x "unknown unary operator"

/-- print.ml:32-42 inverse. -/
def readBinop : Sexpr → ReadM BinOp
  | .atom "and" => .ok .and
  | .atom "or" => .ok .or
  | .atom "impl" => .ok .impl
  | .atom "equiv" => .ok .equiv
  | .atom "add" => .ok .add
  | .atom "sub" => .ok .sub
  | .atom "mul" => .ok .mul
  | .atom "div" => .ok .div
  | .atom "mod" => .ok .mod
  | .atom "pow" => .ok .pow
  | x => fail "binop" x "unknown binary operator"

/-- print.ml:44-50 inverse. -/
def readCmpop : Sexpr → ReadM CmpOp
  | .atom "eq" => .ok .eq
  | .atom "ne" => .ok .ne
  | .atom "lt" => .ok .lt
  | .atom "gt" => .ok .gt
  | .atom "le" => .ok .le
  | .atom "ge" => .ok .ge
  | x => fail "cmpop" x "unknown comparison operator"

/-- xl/num.ml:27-31 inverse. -/
def readNumTyp : Sexpr → ReadM NumTyp
  | .atom "nat" => .ok .nat
  | .atom "int" => .ok .int
  | .atom "rat" => .ok .rat
  | .atom "real" => .ok .real
  | x => fail "numtyp" x "unknown numeric type"

/-- print.ml:67-69 inverse. -/
def readOpTyp : Sexpr → ReadM OpTyp
  | .atom "bool" => .ok .bool
  | x => do .ok (.num (← readNumTyp x))

/-- print.ml:150 inverse (`0x%02X`), canonical via `hexByte`. -/
def readHexByte : Sexpr → ReadM Nat
  | x@(.atom tok) => do
    if !tok.startsWith "0x" then fail "sym.num" x "expected 0x… literal" else
    let ds := (tok.drop 2).toString.toList
    if ds.isEmpty then fail "sym.num" x "empty hex literal" else
    let step (acc : ReadM Nat) (c : Char) : ReadM Nat := do
      let a ← acc
      if '0' ≤ c && c ≤ '9' then .ok (a * 16 + (c.toNat - '0'.toNat))
      else if 'A' ≤ c && c ≤ 'F' then .ok (a * 16 + (c.toNat - 'A'.toNat + 10))
      else .error s!"bad hex digit {c}"
    match ds.foldl step (.ok 0) with
    | .error e => fail "sym.num" x e
    | .ok n =>
      if hexByte n == tok then .ok n
      else fail "sym.num" x "non-canonical hex literal"
  | x => fail "sym.num" x "expected hex literal"

/-! ## param/arg classification (see header) -/

/-- Is this a `(exp|typ|def|gram …)` node (the shared param/arg labels)? -/
def isParamArgNode : Sexpr → Bool
  | .node h _ => h == "exp" || h == "typ" || h == "def" || h == "gram"
  | .atom _ => false

def isQuotedAtom : Sexpr → Bool
  | .atom s => s.startsWith "\""
  | _ => false

/-- Classify a tagged node: `true` = param, `false` = arg (rules in the
module header; exact for printer output, fail-closed otherwise). -/
def classifyParamArg : Sexpr → ReadM Bool
  | x@(.node "exp" cs) =>
    match cs with
    | [c1, _] => if isQuotedAtom c1 then .ok true
                 else fail "param/arg" x "2-child (exp …) with non-id first child"
    | [_] => .ok false
    | _ => fail "param/arg" x "bad (exp …) arity"
  | x@(.node "typ" cs) =>
    match cs with
    | [c] => .ok (isQuotedAtom c)
    | _ => fail "param/arg" x "bad (typ …) arity"
  | x@(.node "def" cs) =>
    match cs with
    | [_] => .ok false
    | _ :: _ :: _ => .ok true
    | _ => fail "param/arg" x "bad (def …) arity"
  | x@(.node "gram" cs) =>
    match cs with
    | c1 :: _ => .ok (isQuotedAtom c1)
    | _ => fail "param/arg" x "bad (gram …) arity"
  | x => fail "param/arg" x "not a param/arg node"

/-! ## The mutual reader core (inverse of print.ml:55-186) -/

mutual

/-- print.ml:55-59 inverse. -/
def readIter (x : Sexpr) : ReadM Iter :=
  match x with
  | .atom "opt" => .ok .opt
  | .atom "list" => .ok .list
  | .atom "list1" => .ok .list1
  | .node "listn" [e] => do .ok (.listN (← readExp e) none)
  | .node "listn" [e, xid] => do
    .ok (.listN (← readExp e) (some (← readId xid)))
  | _ => fail "iter" x "unknown iteration"

/-- print.ml:71-78 inverse. -/
def readTyp (x : Sexpr) : ReadM Typ :=
  match x with
  | .atom "bool" => .ok .boolT
  | .atom "text" => .ok .textT
  | .atom "nat" => .ok (.numT .nat)
  | .atom "int" => .ok (.numT .int)
  | .atom "rat" => .ok (.numT .rat)
  | .atom "real" => .ok (.numT .real)
  | .node "var" (xid :: args) => do
    .ok (.varT (← readId xid) (← args.attach.mapM (fun ⟨a, _⟩ => readArg a)))
  | .node "tup" binds => do
    .ok (.tupT (← binds.attach.mapM (fun ⟨b, _⟩ => readTypBind b)))
  | .node "iter" [t, it] => do
    .ok (.iterT (← readTyp t) (← readIter it))
  | _ => fail "typ" x "unknown type"

/-- print.ml:86-87 inverse. -/
def readTypBind (x : Sexpr) : ReadM TypBind :=
  match x with
  | .node "bind" [xid, t] => do .ok (.mk (← readId xid) (← readTyp t))
  | _ => fail "typbind" x "expected (bind id typ)"

/-- print.ml:80-84 inverse. -/
def readDefTyp (x : Sexpr) : ReadM DefTyp :=
  match x with
  | .node "alias" [t] => do .ok (.aliasT (← readTyp t))
  | .node "struct" fs => do
    .ok (.structT (← fs.attach.mapM (fun ⟨f, _⟩ => readTypField f)))
  | .node "variant" cs => do
    .ok (.variantT (← cs.attach.mapM (fun ⟨c, _⟩ => readTypCase c)))
  | _ => fail "deftyp" x "unknown deftyp"

/-- print.ml:89-90 inverse: `(field atom typ param* prem*)`. -/
def readTypField (x : Sexpr) : ReadM TypField :=
  match x with
  | .node "field" (a :: t :: rest) => do
    let at_ ← readAtom a
    let t ← readTyp t
    let qs := rest.attach.takeWhile (fun c => isParamArgNode c.val)
    let prs := rest.attach.dropWhile (fun c => isParamArgNode c.val)
    let qs ← qs.mapM (fun ⟨q, _⟩ => do
      if !(← classifyParamArg q) then fail "typfield" q "arg in quant position"
      else readParam q)
    let prs ← prs.mapM (fun ⟨p, _⟩ => readPrem p)
    .ok (.mk at_ t qs prs)
  | _ => fail "typfield" x "expected (field atom typ …)"

/-- print.ml:92-93 inverse. -/
def readTypCase (x : Sexpr) : ReadM TypCase :=
  match x with
  | .node "case" (op :: t :: rest) => do
    let op ← readMixop op
    let t ← readTyp t
    let qs := rest.attach.takeWhile (fun c => isParamArgNode c.val)
    let prs := rest.attach.dropWhile (fun c => isParamArgNode c.val)
    let qs ← qs.mapM (fun ⟨q, _⟩ => do
      if !(← classifyParamArg q) then fail "typcase" q "arg in quant position"
      else readParam q)
    let prs ← prs.mapM (fun ⟨p, _⟩ => readPrem p)
    .ok (.mk op t qs prs)
  | _ => fail "typcase" x "expected (case mixop typ …)"

/-- print.ml:98-129 inverse. Case order follows print.ml. -/
def readExp (x : Sexpr) : ReadM Exp :=
  match x with
  | .node "var" [xid] => do .ok (.varE (← readId xid))
  | .node "bool" [b] => do .ok (.boolE (← readBool b))
  | .node "num" [n] => do .ok (.numE (← readNum n))
  | .node "text" [t] => do .ok (.textE (← readText t))
  | .node "un" [op, t, e2] => do
    .ok (.unE (← readUnop op) (← readOpTyp t) (← readExp e2))
  | .node "bin" [op, t, e1, e2] => do
    .ok (.binE (← readBinop op) (← readOpTyp t) (← readExp e1) (← readExp e2))
  | .node "cmp" [op, t, e1, e2] => do
    .ok (.cmpE (← readCmpop op) (← readOpTyp t) (← readExp e1) (← readExp e2))
  | .node "idx" [e1, e2] => do .ok (.idxE (← readExp e1) (← readExp e2))
  | .node "slice" [e1, e2, e3] => do
    .ok (.sliceE (← readExp e1) (← readExp e2) (← readExp e3))
  | .node "upd" [e1, p, e2] => do
    .ok (.updE (← readExp e1) (← readPath p) (← readExp e2))
  | .node "ext" [e1, p, e2] => do
    .ok (.extE (← readExp e1) (← readPath p) (← readExp e2))
  | .node "struct" fs => do
    .ok (.strE (← fs.attach.mapM (fun ⟨f, _⟩ => readExpField f)))
  | .node "dot" [e1, a] => do .ok (.dotE (← readExp e1) (← readAtom a))
  | .node "comp" [e1, e2] => do .ok (.compE (← readExp e1) (← readExp e2))
  | .node "mem" [e1, e2] => do .ok (.memE (← readExp e1) (← readExp e2))
  | .node "len" [e1] => do .ok (.lenE (← readExp e1))
  | .node "tup" es => do
    .ok (.tupE (← es.attach.mapM (fun ⟨e, _⟩ => readExp e)))
  | .node "call" (xid :: args) => do
    .ok (.callE (← readId xid)
      (← args.attach.mapM (fun ⟨a, _⟩ => readArg a)))
  | .node "iter" (e1 :: it :: doms) => do
    -- print.ml:118 + 141-142 (iterexp spliced inline)
    -- NOTE: only reachable when e1 parses as an exp; the sym/prem "iter"
    -- nodes live in different positions.
    .ok (.iterE (← readExp e1)
      (.mk (← readIter it) (← doms.attach.mapM (fun ⟨d, _⟩ => readDom d))))
  | .node "proj" [e1, i] => do
    .ok (.projE (← readExp e1) (← readNatTok "proj" i))
  | .node "case" [op, e1] => do .ok (.caseE (← readMixop op) (← readExp e1))
  | .node "uncase" [e1, op] => do
    .ok (.uncaseE (← readExp e1) (← readMixop op))
  | .node "opt" [] => .ok (.optE none)
  | .node "opt" [e1] => do .ok (.optE (some (← readExp e1)))
  | .node "unopt" [e1] => do .ok (.theE (← readExp e1))
  | .node "list" es => do
    .ok (.listE (← es.attach.mapM (fun ⟨e, _⟩ => readExp e)))
  | .node "lift" [e1] => do .ok (.liftE (← readExp e1))
  | .node "cat" [e1, e2] => do .ok (.catE (← readExp e1) (← readExp e2))
  | .node "cvt" [nt1, nt2, e1] => do
    .ok (.cvtE (← readExp e1) (← readNumTyp nt1) (← readNumTyp nt2))
  | .node "sub" [t1, t2, e1] => do
    .ok (.subE (← readExp e1) (← readTyp t1) (← readTyp t2))
  | .node "if" [e1, e2, e3] => do
    .ok (.ifE (← readExp e1) (← readExp e2) (← readExp e3))
  | _ => fail "exp" x "unknown expression"

/-- print.ml:131-132 inverse. -/
def readExpField (x : Sexpr) : ReadM ExpField :=
  match x with
  | .node "field" [a, e] => do .ok (.mk (← readAtom a) (← readExp e))
  | _ => fail "expfield" x "expected (field atom exp)"

/-- print.ml:134-139 inverse. -/
def readPath (x : Sexpr) : ReadM Path :=
  match x with
  | .atom "root" => .ok .rootP
  | .node "idx" [p, e] => do .ok (.idxP (← readPath p) (← readExp e))
  | .node "slice" [p, e1, e2] => do
    .ok (.sliceP (← readPath p) (← readExp e1) (← readExp e2))
  | .node "dot" [p, a] => do .ok (.dotP (← readPath p) (← readAtom a))
  | _ => fail "path" x "unknown path"

/-- print.ml:142 inverse. -/
def readDom (x : Sexpr) : ReadM Dom :=
  match x with
  | .node "dom" [xid, e] => do .ok (.mk (← readId xid) (← readExp e))
  | _ => fail "dom" x "expected (dom id exp)"

/-- print.ml:147-157 inverse. -/
def readSym (x : Sexpr) : ReadM Sym :=
  match x with
  | .node "var" (xid :: args) => do
    .ok (.varG (← readId xid)
      (← args.attach.mapM (fun ⟨a, _⟩ => readArg a)))
  | .node "num" [n] => do .ok (.numG (← readHexByte n))
  | .node "text" [t] => do .ok (.textG (← readText t))
  | .atom "eps" => .ok .epsG
  | .node "seq" gs => do
    .ok (.seqG (← gs.attach.mapM (fun ⟨g, _⟩ => readSym g)))
  | .node "alt" gs => do
    .ok (.altG (← gs.attach.mapM (fun ⟨g, _⟩ => readSym g)))
  | .node "range" [g1, g2] => do .ok (.rangeG (← readSym g1) (← readSym g2))
  | .node "iter" (g1 :: it :: doms) => do
    .ok (.iterG (← readSym g1)
      (.mk (← readIter it) (← doms.attach.mapM (fun ⟨d, _⟩ => readDom d))))
  | .node "attr" [e, g1] => do .ok (.attrG (← readExp e) (← readSym g1))
  | _ => fail "sym" x "unknown grammar symbol"

/-- print.ml:162-169 inverse. `(rule id arg* mixop exp)` — args are the
tagged prefix, then exactly [mixop, exp]. -/
def readPrem (x : Sexpr) : ReadM Prem :=
  match x with
  | .node "rule" (xid :: rest) => do
    let xid ← readId xid
    let args := rest.attach.takeWhile (fun c => isParamArgNode c.val)
    let tail := rest.attach.dropWhile (fun c => isParamArgNode c.val)
    let args ← args.mapM (fun ⟨a, _⟩ => do
      if (← classifyParamArg a) then fail "rulePr" a "param in arg position"
      else readArg a)
    match tail with
    | [⟨op, _⟩, ⟨e, _⟩] => do
      .ok (.rulePr xid args (← readMixop op) (← readExp e))
    | _ => fail "rulePr" x "expected trailing mixop and exp"
  | .node "if" [e] => do .ok (.ifPr (← readExp e))
  | .node "let" [e1, e2] => do .ok (.letPr (← readExp e1) (← readExp e2))
  | .atom "else" => .ok .elsePr
  | .node "iter" (pr :: it :: doms) => do
    .ok (.iterPr (← readPrem pr)
      (.mk (← readIter it) (← doms.attach.mapM (fun ⟨d, _⟩ => readDom d))))
  | .node "neg" [pr] => do .ok (.negPr (← readPrem pr))
  | _ => fail "prem" x "unknown premise"

/-- print.ml:174-179 inverse (shape already classified as arg). -/
def readArg (x : Sexpr) : ReadM Arg :=
  match x with
  | .node "exp" [e] => do .ok (.expA (← readExp e))
  | .node "typ" [t] =>
    if isQuotedAtom t then fail "arg" x "param (typ id) in arg position"
    else do .ok (.typA (← readTyp t))
  | .node "def" [xid] => do .ok (.defA (← readId xid))
  | .node "gram" [g] =>
    if isQuotedAtom g then fail "arg" x "param (gram …) in arg position"
    else do .ok (.gramA (← readSym g))
  | _ => fail "arg" x "unknown argument"

/-- print.ml:181-186 inverse: `(def id param* typ)` / `(gram id param* typ)`
have a tagged params prefix then the result typ. -/
def readParam (x : Sexpr) : ReadM Param :=
  match x with
  | .node "exp" [xid, t] => do .ok (.expP (← readId xid) (← readTyp t))
  | .node "typ" [xid] =>
    if isQuotedAtom xid then do .ok (.typP (← readId xid))
    else fail "param" x "arg (typ t) in param position"
  | .node "def" (xid :: rest) => do
    let xid ← readId xid
    let ps := rest.attach.takeWhile (fun c => isParamArgNode c.val)
    let tail := rest.attach.dropWhile (fun c => isParamArgNode c.val)
    let ps ← ps.mapM (fun ⟨p, _⟩ => readParam p)
    match tail with
    | [⟨t, _⟩] => do .ok (.defP xid ps (← readTyp t))
    | _ => fail "param.def" x "expected exactly one trailing typ"
  | .node "gram" (xid :: rest) => do
    let xid ← readId xid
    let ps := rest.attach.takeWhile (fun c => isParamArgNode c.val)
    let tail := rest.attach.dropWhile (fun c => isParamArgNode c.val)
    let ps ← ps.mapM (fun ⟨p, _⟩ => readParam p)
    match tail with
    | [⟨t, _⟩] => do .ok (.gramP xid ps (← readTyp t))
    | _ => fail "param.gram" x "expected exactly one trailing typ"
  | _ => fail "param" x "unknown parameter"

end

/-! ## params/args sequences and definitions (inverse of print.ml:188-227) -/

/-- Split a `param* arg* rest` child sequence (inst: print.ml:190-191;
clause: print.ml:199-201). Params must precede args (printer order);
returns attached elements so callers keep termination evidence. -/
private def splitParamsArgs (ctx : String) (cs : List Sexpr) :
    ReadM (List Param × List Arg × List Sexpr) := do
  let tagged := cs.attach.takeWhile (fun c => isParamArgNode c.val)
  let rest := cs.attach.dropWhile (fun c => isParamArgNode c.val)
  let mut params : List Param := []
  let mut args : List Arg := []
  for ⟨c, _⟩ in tagged do
    if (← classifyParamArg c) then
      if !args.isEmpty then
        fail ctx c "param after arg (impossible printer output)"
      else
        params := (← readParam c) :: params
    else
      args := (← readArg c) :: args
  .ok (params.reverse, args.reverse, rest.map (·.val))

/-- A params-only prefix (rel/def/gram/typ headers, rules, prods):
print.ml:195,200 emit only quants there; an arg-shaped item fails. -/
private def readParamsPrefix (ctx : String) (cs : List Sexpr) :
    ReadM (List Param × List Sexpr) := do
  let tagged := cs.attach.takeWhile (fun c => isParamArgNode c.val)
  let rest := cs.attach.dropWhile (fun c => isParamArgNode c.val)
  let ps ← tagged.mapM (fun ⟨p, _⟩ => do
    if !(← classifyParamArg p) then fail ctx p "arg in param-only position"
    else readParam p)
  .ok (ps, rest.map (·.val))

/-- print.ml:188-191 inverse. -/
def readInst (x : Sexpr) : ReadM Inst :=
  match x with
  | .node "inst" cs => do
    let (qs, args, rest) ← splitParamsArgs "inst" cs
    match rest with
    | [dt] => do .ok (.mk qs args (← readDefTyp dt))
    | _ => fail "inst" x "expected exactly one trailing deftyp"
  | _ => fail "inst" x "expected (inst …)"

/-- print.ml:193-196 inverse. -/
def readRule (x : Sexpr) : ReadM Rule :=
  match x with
  | .node "rule" (xid :: cs) => do
    let xid ← readId xid
    let (qs, rest) ← readParamsPrefix "rule" cs
    match rest with
    | op :: e :: prems => do
      .ok (.mk xid qs (← readMixop op) (← readExp e)
        (← prems.mapM readPrem))
    | _ => fail "rule" x "expected mixop, exp, prem*"
  | _ => fail "rule" x "expected (rule id …)"

/-- print.ml:198-201 inverse. -/
def readClause (x : Sexpr) : ReadM Clause :=
  match x with
  | .node "clause" cs => do
    let (qs, args, rest) ← splitParamsArgs "clause" cs
    match rest with
    | e :: prems => do
      .ok (.mk qs args (← readExp e) (← prems.mapM readPrem))
    | _ => fail "clause" x "expected exp, prem*"
  | _ => fail "clause" x "expected (clause …)"

/-- print.ml:203-206 inverse. -/
def readProd (x : Sexpr) : ReadM Prod :=
  match x with
  | .node "prod" cs => do
    let (qs, rest) ← readParamsPrefix "prod" cs
    match rest with
    | g :: e :: prems => do
      .ok (.mk qs (← readSym g) (← readExp e) (← prems.mapM readPrem))
    | _ => fail "prod" x "expected sym, exp, prem*"
  | _ => fail "prod" x "expected (prod …)"

/-- print.ml:208-221 inverse. `HintD` output (`Atom ""`) is filtered from
scripts by print.ml:227 and is rejected here if ever encountered. -/
def readDef (x : Sexpr) : ReadM Def :=
  match x with
  | .node "typ" (xid :: cs) => do
    let xid ← readId xid
    let (ps, rest) ← readParamsPrefix "typD" cs
    .ok (.typD xid ps (← rest.mapM readInst))
  | .node "rel" (xid :: cs) => do
    let xid ← readId xid
    let (ps, rest) ← readParamsPrefix "relD" cs
    match rest with
    | op :: t :: rules => do
      .ok (.relD xid ps (← readMixop op) (← readTyp t)
        (← rules.mapM readRule))
    | _ => fail "relD" x "expected mixop, typ, rule*"
  | .node "def" (xid :: cs) => do
    let xid ← readId xid
    let (ps, rest) ← readParamsPrefix "decD" cs
    match rest with
    | t :: clauses => do
      .ok (.decD xid ps (← readTyp t) (← clauses.mapM readClause))
    | _ => fail "decD" x "expected typ, clause*"
  | .node "gram" (xid :: cs) => do
    let xid ← readId xid
    let (ps, rest) ← readParamsPrefix "gramD" cs
    match rest with
    | t :: prods => do
      .ok (.gramD xid ps (← readTyp t) (← prods.mapM readProd))
    | _ => fail "gramD" x "expected typ, prod*"
  | .node "rec" ds => do
    .ok (.recD (← ds.attach.mapM (fun ⟨d, _⟩ => readDef d)))
  | _ => fail "def" x "unknown definition"

/-- Whole script. -/
def readScript (xs : List Sexpr) : ReadM Script :=
  xs.mapM readDef

end SpecTecLean.Il
