# Backlog (not a journal — done items are deleted; narrative lives in
# the arc charters)

- [USER 2026-08-20] **Compiled-vs-slow correctness proof.** Once a
  compiled execution path exists (an il2al-style port) alongside the
  rule-direct slow engine (SpecTecLean/Il/Rel.lean), their agreement
  should be a THEOREM (small compiler-correctness proof), not a test —
  per the no-internal-trust-gaps doctrine. Candidate future arc.
- [AGENT 2026-08-20] Upstream report candidates: eq.ml IfE/NegPr
  poly-equality fallback (Eq.lean header); valid.ml proj_tup_typ
  countdown-index binding (Valid.lean); subst.ml optimization-wrapper
  shadowing as a correctness-relevant subtlety worth documenting
  upstream. Fuller write-ups for the stage-7 findings live in
  docs/findings/ ([USER 2026-08-21] directive): IterE-opt unwrapped
  reduction, reduce_exp_call body substitution, \$allocmodule premise
  order, eta_iter_exp assert reachability.
- [AGENT 2026-08-21] **Runner throughput (next-arc decision).** The
  rule-direct engine is correct on the pilot corpus but ~1s/Step:
  O(|store|) term walks are inherent to store-in-term rewriting without
  hash-consing. Sound escalations, both architectural: (a) pervasive
  hash-consing of the IL AST (O(1) eq/hash, enables real memoization —
  a pointer-keyed memo prototype benchmarked 20x in isolation but
  regressed in vivo for undiagnosed reasons; lead recorded in the arc
  log); (b) upstream-AL-style store indirection (addresses + threaded
  store), trading against direct-rule fidelity. Decide at arc-3
  chartering.
- [AGENT 2026-08-20] IterPr-over-RulePr premises are classified
  not-applicable by Rel.checkPrems (falls to Eval.reducePrem → unknown);
  extend when a wast case needs it.
