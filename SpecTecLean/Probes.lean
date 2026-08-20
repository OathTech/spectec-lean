import SpecTecLean.Il.OfSexpr
/-!
Build-time probes, executed by `lake build` (hence by every `scripts/ci`
run). NOTE: `#guard` is UNTRUSTED-EVALUATOR checking — these are TESTS,
never to be described as kernel-checked (sibling doctrine, cerberus
2026-08-20).
-/

namespace SpecTecLean.Probes

open SpecTecLean SpecTecLean.Il

private def mixopOf (s : String) : Option Xl.Mixop :=
  match Sexpr.parse s.toUTF8 with
  | .ok [x] => (readMixop x).toOption
  | _ => none

-- D3 DONE probe: these two mixops COLLIDE under the old string encoding
-- (`Mixop.to_string` prints both as `x` — the `Seq (Atom a :: tail) when
-- List.for_all is_arg tail` special case, xl/mixop.ml:91-93); the
-- structured dump distinguishes them.
#guard mixopOf "(seq (a \"x\"))\n" != mixopOf "(seq (a \"x\") %)\n"
#guard (mixopOf "(seq (a \"x\"))\n").isSome
#guard (mixopOf "(seq (a \"x\") %)\n").isSome

-- Fixed-atom name table round-trips (spot checks).
#guard (readAtom (.node "s" [.atom "sqarrow"])).toOption
    == some Xl.Atom.sqArrow
#guard (readAtom (.node "s" [.atom "bogusname"])).toOption == none

end SpecTecLean.Probes
