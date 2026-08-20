/-!
Byte-exact mirror of OCaml's `String.escaped` (used by backend-ast/print.ml:12
`text t = Atom ("\"" ^ String.escaped t ^ "\"")`) and its inverse.

OCaml `String.escaped` (stdlib string.ml, OCaml 5.4): per byte,
  '"'  -> \"      '\\' -> \\\\
  '\n' -> \\n     '\t' -> \\t     '\r' -> \\r     '\b' -> \\b
  bytes 32..126 (other than the above) -> themselves
  everything else -> \DDD (three-digit DECIMAL byte value)

We work on UTF-8 bytes (OCaml strings are byte strings; the dump's quoted
atoms are the escaped bytes of the original). `unescape` fails closed: any
escape sequence `String.escaped` cannot produce, or a decoded byte sequence
that is not valid UTF-8, is an error.
-/

namespace SpecTecLean.OcamlEscape

/-- Mirror of OCaml `String.escaped`, byte-wise over the UTF-8 encoding. -/
def escape (s : String) : String := Id.run do
  let mut out := ""
  for b in s.toUTF8 do
    if b == 34 then out := out ++ "\\\""        -- '"'
    else if b == 92 then out := out ++ "\\\\"   -- '\\'
    else if b == 10 then out := out ++ "\\n"
    else if b == 9  then out := out ++ "\\t"
    else if b == 13 then out := out ++ "\\r"
    else if b == 8  then out := out ++ "\\b"
    else if 32 ≤ b && b ≤ 126 then out := out.push (Char.ofNat b.toNat)
    else
      -- \DDD, three-digit decimal
      let n := b.toNat
      out := out ++ "\\" ++ (if n < 10 then "00" else if n < 100 then "0" else "")
                 ++ toString n
  return out

private def digit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none

/-- Inverse of `escape`. Input is the escaped text WITHOUT surrounding
quotes. Fails closed on anything `escape` cannot emit. -/
def unescape (s : String) : Except String String := do
  let cs := s.toList
  let bytes ← go cs (ByteArray.emptyWithCapacity s.length)
  match String.fromUTF8? bytes with
  | some out => .ok out
  | none => .error s!"unescaped bytes are not valid UTF-8: {s}"
where
  go : List Char → ByteArray → Except String ByteArray
    | [], acc => .ok acc
    | '\\' :: rest, acc =>
      match rest with
      | '"' :: cs => go cs (acc.push 34)
      | '\\' :: cs => go cs (acc.push 92)
      | 'n' :: cs => go cs (acc.push 10)
      | 't' :: cs => go cs (acc.push 9)
      | 'r' :: cs => go cs (acc.push 13)
      | 'b' :: cs => go cs (acc.push 8)
      | d1 :: d2 :: d3 :: cs =>
        match digit? d1, digit? d2, digit? d3 with
        | some a, some b, some c =>
          let n := a * 100 + b * 10 + c
          if n < 256 then go cs (acc.push n.toUInt8)
          else .error s!"escape \\{d1}{d2}{d3} out of byte range"
        | _, _, _ => .error s!"invalid escape sequence \\{d1}"
      | _ => .error "dangling backslash"
    | c :: cs, acc =>
      if 32 ≤ c.toNat && c.toNat ≤ 126 then go cs (acc.push c.toNat.toUInt8)
      else .error s!"raw byte {c.toNat} in escaped text"

/-- Quote + escape: the exact form of a quoted atom in the dump
(print.ml:12). -/
def quote (s : String) : String := "\"" ++ escape s ++ "\""

/-- Strip quotes + unescape: read a quoted atom token (raw, as stored by
the Sexpr layer). Fails closed if the token is not quote-delimited. -/
def unquote (tok : String) : Except String String :=
  if tok.length ≥ 2 && tok.startsWith "\"" && tok.endsWith "\"" then
    unescape ((tok.toRawSubstring.drop 1).dropRight 1).toString
  else
    .error s!"expected quoted atom, got: {tok}"

end SpecTecLean.OcamlEscape
