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

/-- Validate a dumped IL script (arc-2 stage 4; valid.ml mirror).
Default fuel is generous scaffolding — exhaustion is a loud error. -/
def cmdValidate (path : String) (fuel : Nat) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  match Sexpr.parse input with
  | .error e => IO.eprintln s!"SEXPR PARSE FAIL {path}: {e}"; return 1
  | .ok xs =>
    match Il.readScript xs with
    | .error e => IO.eprintln s!"IL READ FAIL {path}: {e}"; return 1
    | .ok script =>
      match (Il.Valid.validScript fuel script).run {} with
      | .ok _ =>
        IO.println s!"validate OK: {path} ({script.length} defs)"
        return 0
      | .error (.error msg) =>
        IO.eprintln s!"VALIDATE FAIL {path}: {msg}"; return 1
      | .error .fuel =>
        IO.eprintln s!"VALIDATE FUEL EXHAUSTED {path} (fuel {fuel})"; return 1
      | .error .irred =>
        IO.eprintln s!"VALIDATE FAIL {path}: irreducible"; return 1
      | .error (.failure msg) =>
        IO.eprintln s!"VALIDATE FAIL {path}: internal failure {msg}"; return 1

/-- Debug: validate def-by-def, printing progress (loop isolation). -/
def cmdValidateTrace (path : String) (fuel : Nat) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  match Sexpr.parse input with
  | .error e => IO.eprintln s!"SEXPR PARSE FAIL {path}: {e}"; return 1
  | .ok xs =>
    match Il.readScript xs with
    | .error e => IO.eprintln s!"IL READ FAIL {path}: {e}"; return 1
    | .ok script => do
      let mut env := Il.Env.empty
      let mut st : Il.Fresh.St := {}
      let mut i := 0
      for d in script do
        let nm := match d with
          | .typD x _ _ _ => s!"typ {x}"
          | .relD x _ _ _ _ _ => s!"rel {x}"
          | .decD x _ _ _ _ => s!"def {x}"
          | .gramD x _ _ _ _ => s!"gram {x}"
          | .recD _ _ => "rec"
        IO.println s!"[{i}] {nm}"
        (← IO.getStdout).flush
        match (Il.Valid.validDef env fuel d).run st with
        | .ok (env', st') => env := env'; st := st'
        | .error e => IO.eprintln s!"  FAIL: {reprStr e}"; return 1
        i := i + 1
      IO.println "validate-trace OK"
      return 0

/-- Stage-6 smoke: derive Step_pure on [NOP] (expect []). -/
def cmdDeriveSmoke (path : String) : IO UInt32 := do
  let input ← IO.FS.readBinFile path
  match Sexpr.parse input with
  | .error e => IO.eprintln s!"SEXPR PARSE FAIL: {e}"; return 1
  | .ok xs =>
    match Il.readScript xs with
    | .error e => IO.eprintln s!"IL READ FAIL: {e}"; return 1
    | .ok script =>
      let env := Il.Env.ofScript script
      let instrT : Il.Typ := .varT "instr" []
      let nop : Il.Exp := .mk
        (.caseE (.atom (.atom "NOP")) (.mk (.tupE []) (.tupT [])))
        instrT
      let ins : Il.Exp := .mk (.listE [nop]) (.iterT instrT .list)
      match env.findRel? "Step_pure" with
      | none => IO.eprintln "Step_pure not found"; return 1
      | some (_, mixop, _, rules) =>
        match (Il.Rel.derive env 100000 "Step_pure" mixop rules [ins] 1).run {} with
        | .ok (.ok outs, _) =>
          IO.println s!"derive OK: {outs.length} outputs"
          for o in outs do
            IO.println ((SpecTecLean.Sexpr.pp 0 200 (Il.expToSexpr o)).2)
          return 0
        | .ok (.noRule, _) => IO.eprintln "derive: no rule applies"; return 1
        | .ok (.stuck m, _) => IO.eprintln s!"derive: stuck {m}"; return 1
        | .error e => IO.eprintln s!"derive: {reprStr e}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["derive-smoke", path] => cmdDeriveSmoke path
  | ["validate-trace", path, f] => cmdValidateTrace path (f.toNat!)
  | ["roundtrip-sexpr", path] => cmdRoundtripSexpr path
  | ["roundtrip", path] => cmdRoundtrip path
  | ["format", path] => cmdFormat path
  | ["validate", path] => cmdValidate path 1000000
  | ["validate", path, f] => cmdValidate path (f.toNat!)
  | _ =>
    IO.eprintln "usage: spectecil (roundtrip|roundtrip-sexpr) <file>"
    return 2
