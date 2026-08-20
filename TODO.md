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
  upstream.
- [AGENT 2026-08-20] IterPr-over-RulePr premises are classified
  not-applicable by Rel.checkPrems (falls to Eval.reducePrem → unknown);
  extend when a wast case needs it.
