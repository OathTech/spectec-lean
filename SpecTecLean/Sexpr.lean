/-!
S-expressions as produced by the OCaml spectec `--ast` backend.

Mirrors `deps/spectec/spectec/src/util/sexpr.ml` (spectec @ acc6e834; see
`baselines/upstream-pins.txt`). The layout algorithm (`Sexpr.pp`) is a
line-for-line mirror — byte-identical output is a gate requirement.

Deliberate divergences (mirror doctrine, CLAUDE.md):
- `Atom` here carries the RAW TOKEN TEXT: a quoted atom keeps its quotes and
  escape sequences verbatim. The OCaml side pre-escapes at construction time
  (backend-ast/print.ml:12 `text`); we defer interpretation to the IL layer
  so that text → Sexpr → text is byte-exact by construction at this layer.
- The OCaml `rope` type (sexpr.ml:3) is an output-buffering device; we build
  `String`s directly. Layout decisions are unaffected (they depend only on
  the `len` arithmetic, mirrored exactly).
- Parsing has no OCaml counterpart to mirror (the OCaml side only prints);
  the tokenizer/parser below is fail-closed: any input outside the exact
  shape `pp` can emit (plus interior whitespace variation) is an error,
  never a skip. Input is required to be printable ASCII on EVERY byte path
  (all `pp` output is: OCaml `String.escaped` maps everything else to
  escape sequences), so `String.length` below coincides with OCaml's
  byte-based `String.length`.
- Known boundary (audit 2026-08-20): `Atom ""` (what `HintD` prints as,
  print.ml:220-221) renders as zero-width text, so a parser cannot see it;
  if one were nested in a `RecD` (top-level ones are filtered,
  print.ml:227; nested ones are believed unreachable per il/free.ml:213 +
  elab.ml:2853-2859), the round-trip byte-compare fails VISIBLY — it can
  never pass silently.
-/

namespace SpecTecLean

inductive Sexpr where
  /-- Bare or quoted token, raw text (quotes/escapes included verbatim). -/
  | atom (s : String)
  /-- `(head child*)` — sexpr.ml:1 `Node of string * sexpr list`. -/
  | node (head : String) (children : List Sexpr)
deriving Repr, BEq, Inhabited

namespace Sexpr

/-! ## Layout (mirror of sexpr.ml:15-32) -/

/-- Mirror of `pp off width` (sexpr.ml:15-23). Returns the FLAT length (even
when the rendering broke — the OCaml `len` is computed before `sep`/`fin`
are chosen, from the children's flat lengths) together with the rendered
text. `len = |s| + #children + (2 + Σ lens)` (sexpr.ml:19). -/
def pp (off width : Nat) : Sexpr → Nat × String
  | .atom s => (s.length, s)
  | .node s xs =>
    let rs := xs.attach.map (fun ⟨x, _⟩ => pp (off + 2) width x)
    let len := s.length + rs.length + rs.foldl (fun a r => a + r.1) 2
    let (sep, fin) :=
      if off + len ≤ width then (" ", "")
      else ("\n  " ++ "".pushn ' ' off, "\n" ++ "".pushn ' ' off)
    (len, rs.foldl (fun acc r => acc ++ sep ++ r.2) ("(" ++ s) ++ fin ++ ")")

/-- Mirror of `Sexpr.to_string` (sexpr.ml:32): rendering plus newline. -/
def render (width : Nat) (x : Sexpr) : String :=
  (pp 0 width x).2 ++ "\n"

/-- The `--ast -o file` byte format (exe-spectec/main.ml:324-328):
each top-level sexpr rendered with a trailing newline, then one extra
final newline. Default width is 80 (backend-ast/config.ml:9). -/
def renderScript (width : Nat) (xs : List Sexpr) : String :=
  String.join (xs.map (render width)) ++ "\n"

/-! ## Tokenizer (fail-closed; no OCaml counterpart — see header) -/

inductive Token where
  | lparen
  | rparen
  /-- Raw atom text; for quoted atoms includes the surrounding quotes. -/
  | atom (s : String)
deriving Repr, BEq

/-- Errors carry a position (byte offset for tokenize, token index after). -/
structure Err where
  pos : Nat
  msg : String
deriving Repr

instance : ToString Err where
  toString e := s!"position {e.pos}: {e.msg}"

private def isBareAtomByte (b : UInt8) : Bool :=
  -- printable ASCII except space, parens, quote
  33 ≤ b && b ≤ 126 && b != 40 && b != 41 && b != 34

/-- Decode a byte slice already checked to be printable ASCII. -/
private def asciiSlice (a : ByteArray) (start stop : Nat) : String :=
  (List.range (stop - start)).foldl
    (fun s k => s.push (Char.ofNat (a.get! (start + k)).toNat)) ""

/-- Scan a quoted atom whose opening quote is at `i`; returns the position
one past the closing quote. A backslash escapes the following byte. -/
private def scanQuoted (a : ByteArray) (i : Nat) : Except Err Nat :=
  go (i + 1)
where
  go (j : Nat) : Except Err Nat :=
    if _h : j < a.size then
      let b := a.get! j
      if b == 34 then .ok (j + 1)                    -- '"'
      else if b == 92 then                           -- '\\'
        if _h2 : j + 1 < a.size then
          let b2 := a.get! (j + 1)
          -- the escaped byte must also be printable ASCII (String.escaped
          -- emits only such; audit 2026-08-20 finding — this branch
          -- previously skipped the check, breaking the ASCII invariant)
          if 32 ≤ b2 && b2 ≤ 126 then go (j + 2)
          else .error ⟨j + 1, s!"non-printable or non-ASCII byte {b2} after backslash"⟩
        else .error ⟨j, "dangling backslash at end of input"⟩
      else if 32 ≤ b && b ≤ 126 then go (j + 1)
      else .error ⟨j, s!"non-printable or non-ASCII byte {b} in string"⟩
    else .error ⟨i, "unterminated string literal"⟩
  termination_by a.size - j

/-- Scan a bare atom starting at `i`; returns one past its last byte. -/
private def scanBare (a : ByteArray) (i : Nat) : Nat :=
  go i
where
  go (j : Nat) : Nat :=
    if _h : j < a.size then
      if isBareAtomByte (a.get! j) then go (j + 1) else j
    else j
  termination_by a.size - j

/-- Tokenize the whole input. Whitespace is space and newline only — the
exact set `pp` emits; anything else fails closed. -/
def tokenize (a : ByteArray) : Except Err (Array Token) :=
  go 0 #[]
where
  go (i : Nat) (acc : Array Token) : Except Err (Array Token) :=
    if _h : i < a.size then
      let b := a.get! i
      if b == 32 || b == 10 then                     -- ' ' '\n'
        go (i + 1) acc
      else if b == 40 then                           -- '('
        go (i + 1) (acc.push .lparen)
      else if b == 41 then                           -- ')'
        go (i + 1) (acc.push .rparen)
      else if b == 34 then                           -- '"'
        match scanQuoted a i with
        | .error e => .error e
        | .ok stop =>
          if _hlt : i < stop then
            go stop (acc.push (.atom (asciiSlice a i stop)))
          else
            .error ⟨i, "internal: scanQuoted did not advance"⟩
      else if isBareAtomByte b then
        let stop := scanBare a i
        if _hlt : i < stop then
          go stop (acc.push (.atom (asciiSlice a i stop)))
        else
          .error ⟨i, "internal: scanBare did not advance"⟩
      else
        .error ⟨i, s!"unexpected byte {b}"⟩
    else
      .ok acc
  termination_by a.size - i

/-! ## Parser (fail-closed) -/

mutual

/-- Parse one sexpr at token index `i`. A node is `( head child* )` with a
BARE head label — backend-ast/print.ml only emits fixed unquoted labels. -/
private def parseOne (ts : Array Token) (i : Nat) :
    Except Err (Sexpr × Nat) :=
  if h : i < ts.size then
    match ts[i] with
    | .atom s => .ok (.atom s, i + 1)
    | .rparen => .error ⟨i, "unexpected `)`"⟩
    | .lparen =>
      if h2 : i + 1 < ts.size then
        match ts[i + 1] with
        | .atom head =>
          if head.startsWith "\"" then
            .error ⟨i + 1, s!"node head must be a bare label, got {head}"⟩
          else
            parseChildren ts head (i + 2) []
        | _ => .error ⟨i + 1, "expected node head label after `(`"⟩
      else .error ⟨i, "unterminated `(` at end of input"⟩
  else .error ⟨i, "unexpected end of input"⟩
  termination_by 2 * (ts.size - i)

/-- Parse children of a node headed `head` until the closing `)`. -/
private def parseChildren (ts : Array Token) (head : String) (j : Nat)
    (acc : List Sexpr) : Except Err (Sexpr × Nat) :=
  if h : j < ts.size then
    match ts[j] with
    | .rparen => .ok (.node head acc.reverse, j + 1)
    | _ =>
      match parseOne ts j with
      | .error e => .error e
      | .ok (x, j') =>
        if hlt : j < j' then
          parseChildren ts head j' (x :: acc)
        else
          .error ⟨j, "internal: parser did not advance"⟩
  else .error ⟨j, "unterminated node (missing `)`)"⟩
  termination_by 2 * (ts.size - j) + 1

end

/-- Parse a whole script: a sequence of top-level sexprs. -/
def parse (a : ByteArray) : Except Err (List Sexpr) :=
  match tokenize a with
  | .error e => .error e
  | .ok ts => go ts 0 []
where
  go (ts : Array Token) (i : Nat) (acc : List Sexpr) :
      Except Err (List Sexpr) :=
    if i < ts.size then
      match parseOne ts i with
      | .error e => .error e
      | .ok (x, i') =>
        if _hlt : i < i' then
          go ts i' (x :: acc)
        else
          .error ⟨i, "internal: parser did not advance"⟩
    else
      .ok acc.reverse
  termination_by ts.size - i

end Sexpr

end SpecTecLean
