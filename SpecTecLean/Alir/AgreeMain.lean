import SpecTecLean.Alir.Agree
import SpecTecLean.Il.OfSexpr
/-! Agreement harness entry (arc-3b lane gate step).
Usage: aliragree <spec.sexpr> — exit 0 iff every pinned case AGREEs. -/

open SpecTecLean SpecTecLean.Il SpecTecLean.Il.Alir

def main (args : List String) : IO UInt32 := do
  let specPath ← match args with
    | [p] => pure p
    | _ => IO.eprintln "usage: aliragree <spec.sexpr>"; return 2
  let input ← IO.FS.readBinFile specPath
  let spec ← match Sexpr.parse input >>= (readScript · |>.mapError (⟨0, ·⟩)) with
    | .ok s => pure s
    | .error e => IO.eprintln s!"SPEC LOAD FAIL: {e}"; return 2
  let env := Env.ofScript spec
  let rows := runAll env 1000000 1000
  let mut bad := 0
  for (name, a, r, verdict) in rows do
    IO.println s!"{name}\t{verdict}"
    if verdict != "AGREE" then
      bad := bad + 1
      IO.println s!"  alir: {a}"
      IO.println s!"  rel:  {r}"
  IO.println s!"SUMMARY cases={rows.length} agree={rows.length - bad} non-agree={bad}"
  return (if bad == 0 then 0 else 1)
