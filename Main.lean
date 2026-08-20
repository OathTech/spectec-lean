import SpecTecLean

open SpecTecLean

/-- Report the first differing byte offset with context, or none. -/
def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    if a.get! i != b.get! i then
      return some i
  if a.size != b.size then return some n
  return none

def diffReport (input output : ByteArray) : String :=
  match firstDiff input output with
  | none => "identical"
  | some i =>
    let ctx (x : ByteArray) : String :=
      let lo := i - 40
      let hi := min x.size (i + 40)
      let bytes := x.extract lo hi
      -- total decode: a slice can split a UTF-8 sequence or carry invalid
      -- bytes (audit 2026-08-20: fromUTF8! panicked here)
      match String.fromUTF8? bytes with
      | some s => s
      | none => s!"(non-UTF8 bytes) {bytes.toList}"
    s!"first difference at byte {i}\n  input:  …{ctx input}…\n  output: …{ctx output}…"

/-- text → Sexpr → text, byte-identical (charter slice 3 gate). -/
def cmdRoundtripSexpr (path : String) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  match Sexpr.parse input with
  | .error e =>
    IO.eprintln s!"PARSE FAIL {path}: {e}"
    return 1
  | .ok xs =>
    let out := (Sexpr.renderScript 80 xs).toUTF8
    if out == input then
      IO.println s!"roundtrip-sexpr OK: {path} ({xs.length} toplevel sexprs, {input.size} bytes)"
      return 0
    else
      IO.eprintln s!"ROUNDTRIP FAIL {path}: {diffReport input out}"
      return 1

/-- text → Sexpr → IL → Sexpr → text, byte-identical (charter DONE gate). -/
def cmdRoundtrip (path : String) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  match Sexpr.parse input with
  | .error e =>
    IO.eprintln s!"SEXPR PARSE FAIL {path}: {e}"
    return 1
  | .ok xs =>
    match Il.readScript xs with
    | .error e =>
      IO.eprintln s!"IL READ FAIL {path}: {e}"
      return 1
    | .ok script =>
      let out := (Sexpr.renderScript 80 (Il.scriptToSexprs script)).toUTF8
      if out == input then
        IO.println s!"roundtrip OK: {path} ({script.length} defs, {input.size} bytes byte-identical)"
        return 0
      else
        IO.eprintln s!"ROUNDTRIP FAIL {path}: {diffReport input out}"
        return 1

/-- Parse + IL-read a file and print its canonical rendering (used to
canonicalize hand-authored corpus content; layout is the printer's). -/
def cmdFormat (path : String) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  match Sexpr.parse input with
  | .error e => IO.eprintln s!"SEXPR PARSE FAIL {path}: {e}"; return 1
  | .ok xs =>
    match Il.readScript xs with
    | .error e => IO.eprintln s!"IL READ FAIL {path}: {e}"; return 1
    | .ok script =>
      IO.print (Sexpr.renderScript 80 (Il.scriptToSexprs script))
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["roundtrip-sexpr", path] => cmdRoundtripSexpr path
  | ["roundtrip", path] => cmdRoundtrip path
  | ["format", path] => cmdFormat path
  | _ =>
    IO.eprintln "usage: spectecil (roundtrip|roundtrip-sexpr) <file>"
    return 2
