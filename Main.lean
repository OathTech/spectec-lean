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
        match (Il.Rel.derive env 100000 [] [] "Step_pure" mixop rules [ins] 1).run {} with
        | .ok (.ok outs, _) =>
          IO.println s!"derive OK: {outs.length} outputs"
          for o in outs do
            IO.println ((SpecTecLean.Sexpr.pp 0 200 (Il.expToSexpr o)).2)
          return 0
        | .ok (.noRule, _) => IO.eprintln "derive: no rule applies"; return 1
        | .ok (.stuck m, _) => IO.eprintln s!"derive: stuck {m}"; return 1
        | .error e => IO.eprintln s!"derive: {reprStr e}"; return 1

/-- Stage 7: run a wast command stream against the spec semantics. -/
def cmdRunWast (specPath cmdsPath : String) (fuel steps : Nat) : IO UInt32 := do
  let specIn ← IO.FS.readBinFile specPath
  let spec ← match Sexpr.parse specIn >>= (Il.readScript · |>.mapError (⟨0, ·⟩)) with
    | .ok s => pure s
    | .error e => IO.eprintln s!"SPEC LOAD FAIL: {e}"; return 2
  -- execution-only engine mode (see Env.guardOpenCalls doc)
  let env := { Il.Env.ofScript spec with guardOpenCalls := true }
  let cmdsIn ← IO.FS.readBinFile cmdsPath
  let cmds ← match Sexpr.parse cmdsIn with
    | .ok cs => pure cs
    | .error e => IO.eprintln s!"CMDS PARSE FAIL: {e}"; return 2
  let mut fresh : Il.Fresh.St := {}
  let valHeads ← match (Il.Runner.variantHeads env fuel (.varT "val" [])).run fresh with
    | .ok (h, st') => fresh := st'; pure h
    | .error e => IO.eprintln s!"valHeads: {reprStr e}"; return 2
  let store0 ← match (Il.Runner.emptyStore env fuel).run fresh with
    | .ok (s, st') => fresh := st'; pure s
    | .error e => IO.eprintln s!"store init: {reprStr e}"; return 2
  let mut st : Il.Runner.St := { store := store0, modinst := none }
  -- Wasm 3.0 script AST: (mod …) defines, (instance) instantiates the
  -- most recent anonymous module (script.ml:60-62)
  let mut pendingMod : Option Il.Exp := none
  let mut counts : List (String × Nat) := []
  let bump := fun (cs : List (String × Nat)) (k : String) =>
    match cs.lookup k with
    | some n => (k, n+1) :: cs.filter (·.1 != k)
    | none => (k, 1) :: cs
  let unq := fun (x : Sexpr) => match x with
    | .atom t => (OcamlEscape.unquote t).toOption.getD t
    | _ => "?"
  let alv := fun (x : Sexpr) => Il.AlValue.ofSexpr x
  let mut i := 0
  for cmd in cmds do
    let t0 ← IO.monoMsNow
    let mut row : String × String := ("", "")
    match cmd with
    | .node "mod" [mv] =>
      match alv mv with
      | .error e => row := ("error", s!"module AL parse: {e}")
      | .ok v =>
        match (Il.AlDecode.decode env fuel v (.varT "module" [])).run fresh with
        | .ok (modE, st') =>
          fresh := st'
          -- FAIL CLOSED on declared imports (audit dim2-3/V2): the
          -- harness has no linker; instantiating with an empty
          -- externaddr vector mis-indexes exports (a demonstrated
          -- silent wrong answer). MODULE payload component 1 is the
          -- import list (2.5-syntax.modules.spectec).
          match Il.Runner.notationComps modE with
          | some comps =>
            match comps[1]? with
            | some impsE =>
              -- the component is list(import) — a singleton-case
              -- notation wrapper around the actual list
              let inner := match (Il.Runner.stripSub impsE).it with
                | .caseE _ pl =>
                  match pl.it with
                  | .tupE [l] => some (Il.Runner.stripSub l)
                  | _ => none
                | .listE es => some (.mk (.listE es) impsE.note)
                | _ => none
              match inner with
              | some (.mk (.listE []) _) =>
                pendingMod := some modE
                row := ("module", "defined")
              | some (.mk (.listE _) _) =>
                pendingMod := none
                row := ("unsupported:imports", "no linker in the harness")
              | _ =>
                pendingMod := none
                row := ("error", "module imports component shape")
            | none =>
              pendingMod := none
              row := ("error", "module payload arity")
          | none =>
            pendingMod := none
            row := ("error", "module shape")
        | .error .fuel => row := ("fuel", "")
        | .error e => row := ("error", reprStr e)
    | .node "instance" [] =>
      match pendingMod with
      | none => row := ("error", "instance with no pending module")
      | some modE =>
        match (do
            let extsE : Il.Exp := .mk (.listE []) (.iterT (.varT "externaddr" []) .list)
            let cfg ← Il.Runner.evalCall env fuel "instantiate"
              [st.store, modE, extsE] (.varT "config" [])
            Il.Runner.runConfig env fuel valHeads steps cfg).run fresh with
        | .ok (.done state _, st') =>
          fresh := st'
          match Il.Runner.stateParts state with
          | some (store', frame) =>
            match Il.Runner.structField frame "MODULE" with
            | some mi =>
              st := { store := store', modinst := some mi }
              row := ("module", "instantiated")
            | none => row := ("error", "frame has no MODULE")
          | none => row := ("error", "state shape")
        | .ok (.trap _, st') => fresh := st'; row := ("error", "instantiation trapped")
        | .ok (.stuck _ m, st') => fresh := st'; row := ("stuck", m)
        | .error .fuel => row := ("fuel", "")
        | .error e => row := ("error", reprStr e)
    | .node "assert_return" [.node "act" ((.atom "invoke") :: nm :: [.node "L" argXs]), .node "L" expXs] =>
      match argXs.mapM alv, expXs.mapM alv with
      | .ok argVs, .ok expVs =>
        match (do
            let (rk, _) ← Il.Runner.runInvoke env fuel steps valHeads st
              (unq nm) argVs
            let expected ← expVs.mapM (fun v =>
              Il.AlDecode.decode env fuel v (.varT "val" []))
            pure (rk, expected)).run fresh with
        | .ok ((.done state results, expected), st') =>
          fresh := st'
          match Il.Runner.stateParts state with
          | some (store', _) => st := { st with store := store' }
          | none => pure ()
          if results.length == expected.length
              && (results.zip expected).all (fun (r, e) =>
                   Il.eqExp r (Il.Runner.stripSub e)) then
            row := ("pass", "")
          else
            row := ("fail", s!"expected {expected.length} vals, mismatch")
        | .ok ((.trap _, _), st') => fresh := st'; row := ("fail", "trapped, expected return")
        | .ok ((.stuck _ m, _), st') => fresh := st'; row := ("stuck", m)
        | .error .fuel => row := ("fuel", "")
        | .error e => row := ("error", reprStr e)
      | _, _ => row := ("error", "AL parse in assert_return")
    | .node "assert_trap" [.node "act" ((.atom "invoke") :: nm :: [.node "L" argXs]), _msg] =>
      match argXs.mapM alv with
      | .ok argVs =>
        match (Il.Runner.runInvoke env fuel steps valHeads st (unq nm) argVs).run fresh with
        | .ok ((.trap _, _), st') => fresh := st'; row := ("pass", "")
        | .ok ((.done _ _, _), st') => fresh := st'; row := ("fail", "returned, expected trap")
        | .ok ((.stuck _ m, _), st') => fresh := st'; row := ("stuck", m)
        | .error .fuel => row := ("fuel", "")
        | .error e => row := ("error", reprStr e)
      | _ => row := ("error", "AL parse in assert_trap")
    | .node "do" [.node "act" ((.atom "invoke") :: nm :: [.node "L" argXs])] =>
      match argXs.mapM alv with
      | .ok argVs =>
        match (Il.Runner.runInvoke env fuel steps valHeads st (unq nm) argVs).run fresh with
        | .ok ((.done state _, _), st') =>
          fresh := st'
          match Il.Runner.stateParts state with
          | some (store', _) => st := { st with store := store' }
          | none => pure ()
          row := ("action", "")
        | .ok (_, st') => fresh := st'; row := ("action", "non-return")
        | .error .fuel => row := ("fuel", "")
        | .error e => row := ("error", reprStr e)
      | _ => row := ("error", "AL parse in do")
    | .node "unsupported" [c, d] =>
      row := (s!"unsupported:{unq c}", unq d)
    | x =>
      row := ("error", s!"unrecognized command {(Sexpr.pp 0 100000 x).2.take 60}")
    let t1 ← IO.monoMsNow
    IO.println s!"{i}	{row.1}	{row.2}	[{t1-t0}ms]"
    (← IO.getStdout).flush
    counts := bump counts row.1
    i := i + 1
  let total := counts.foldl (fun a p => a + p.2) 0
  let summary := String.intercalate " " (counts.map (fun (k, n) => s!"{k}={n}"))
  IO.println s!"SUMMARY total={total} {summary}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run-wast", spec, cmds] => cmdRunWast spec cmds 1000000 10000
  | ["run-wast", spec, cmds, f, st] => cmdRunWast spec cmds (f.toNat!) (st.toNat!)
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
