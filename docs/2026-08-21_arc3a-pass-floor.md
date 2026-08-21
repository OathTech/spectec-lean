# Arc 3a: the pass floor, rule-direct — BLESSED 2026-08-21

Branch: `arc3a-pass-floor` (off `main` after arc-2 lands). Lane owns
`SpecTecLean/Il/*`, `SpecTecLean/Runner.lean`, `SpecTecLean/Al.lean`,
`baselines/`, `scripts/ci` — the core-owner lane (worktree doctrine).

## Objective

Make the RULE-DIRECT engine fast enough to PASS the wasm integer/control
fragment, closing arc-2's one unmet DONE item. This validates the
definitional semantics directly — the artifact the frontend-soundness
theorem quantifies over. The compiled path (arc 3b) is NOT a substitute
for this: theorems hang off the slow engine.

## Strategy (two named cost gaps; the third is arc-3b's)

1. **Store/term representation.** Today configs embed the store as a
   term: O(N²) store growth (funcinst embeds moduleinst by value) and
   O(|store|) walks per reduce/match/eq. Fix candidates, worker
   investigates BOTH and records the decision with measurements before
   committing to either:
   (a) store indirection — state components held behind a handle with
   indexed accessors, justified by the spec's own access discipline
   (rules touch the store only via `$funcinst(z)`-style accessors);
   bisimilarity-by-construction argument REQUIRED in the design note;
   (b) hash-consing/interning of value terms — O(1) eq/hash, O(N)
   dedup'd store, enables effective memoization. Two prior unsafe
   pointer-memo attempts regressed mysteriously (arc-2 log) — any
   unsafe machinery needs an isolated micro-benchmark AND an in-vivo
   measurement before adoption.
2. **Numerics extension (D4 interface, already chartered).** wasm
   arithmetic behind the declared extension interface with a native
   fast path mirroring upstream's interpreter numerics
   (`backend-interpreter`/reference-interpreter semantics), replacing
   bit-level spec-function reduction on the hot path. The slow
   spec-function path REMAINS available; ci gains an agreement probe
   (fast path vs spec-function path on a pinned case set) — fail-closed
   on disagreement.

## DONE (machine-checkable, all of it)

- [ ] **Pass floor**: every harness-classified non-float
      assert_return/assert_trap in the 20 integer/control files (i32,
      i64, int_exprs, int_literals, block, br, br_if, br_table, if,
      loop, return, call, local_get, local_set, local_tee, global, nop,
      unreachable, memory_grow, memory_size) PASSES; count reported,
      derived by the classifier. Zero divergences in this set.
- [ ] Corpus re-classification refresh (`scripts/wast-classify`) with
      new grand totals re-pinned; every class shift vs the arc-2
      baseline explained in the results section.
- [ ] Numerics fast-vs-spec agreement probe green in ci.
- [ ] ci GREEN throughout (round-trips, validator, probes, pilot);
      no gate weakening; representation changes carry an in-code
      bisimilarity/faithfulness note (mirror doctrine).
- [ ] 0 partial/sorry/native_decide; decision log current
      ([AGENT]/[USER]); results section; audit ask posed.

## Hard boundaries

- No AL/il2al work (arc-3b's lane). No upstream bump. Core stays
  language-agnostic: numerics enter ONLY through the extension
  interface; nothing wasm-specific in core namespaces.
- No merge/push; land via the unchanged merge protocol.
- Park-don't-improvise: if a representation change cannot carry an
  honest faithfulness argument, park with the analysis.

## Escape hatches

- If neither representation option reaches the floor: park with
  profiles + a written recommendation (likely "wait for arc-3b"),
  deliver the numerics extension + measurements as the arc.
- If the numerics interface cannot stay language-agnostic: park, record
  the leak, re-scope with the user.
- EMERGENCY EXIT always available (declare nature, park, report).
