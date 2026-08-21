# Arc 2 — the interpreter milestone (charter)

Status: **BLESSED** ([USER] Mike, 2026-08-20: "go ahead an bless the
plan"; goal to be set by the user for the autonomous run). Branch:
`arc2-interpreter-milestone` off `main` @ `4affb2f` (arc 1 merged).
Supersedes the earlier "binding layer + validation" arc-2 sketch by
absorbing it as stages 2-3 ([USER] 2026-08-20: reshape as a longer
autonomous push toward a major counted goal).

## Goal

Push the toolkit from "round-trips the IL" to **"executes SpecTec specs"**:
a faithful-but-slow ([USER]) IL semantics in Lean, validated by
differentially running the Wasm 3.0 spec against the OCaml toolchain on
the pinned test suite (`deps/spectec/test/core`, 97 wast files, 19,841
assertions — scoping probe 2026-08-20). This is objective item (5)
(docs/2026-08-20_objective-go-frontend-soundness.md): the interpreter that
gives SpecTec specs a Lean-native meaning, differential leg 1.

## Stages (each a gated slice or slice-group; commit per slice)

1. **D3 dump patch** (ratified): vendored patch under `patches/` to
   `backend-ast` making the dump lossless — structural mixops + atoms,
   `LetPr` binders, source positions. Applied to the pinned checkout at
   setup (script), recorded in `baselines/upstream-pins.txt`; ALL dump
   sha pins re-pinned with the reason committed. Lean side: `Mixop`/`Atom`
   become structured types mirroring xl/mixop.ml + xl/atom.ml; round-trip
   gate stays byte-identical against the patched printer.
2. **Binding layer**: mirror `il/free.ml`, `il/subst.ml`, `il/eq.ml`,
   `il/env.ml` (+ `il/fresh.ml` if needed). Unit-level differential where
   cheap; mirror citations throughout.
3. **IL validation**: mirror `il/valid.ml`. Gate: all three wasm corpora
   validate green (the elaborator only emits well-formed IL — that IS the
   oracle signal); mutation probes rejected; wired into `scripts/ci`.
4. **Value domain + expression evaluation**: `Val` (constructor trees,
   records, tuples, lists, options, nums, text); closed-term big-step
   eval of pure `Exp`s, fuel-totalized with a loud fuel-exhausted
   sentinel (never a wrong answer). OCaml `il/eval.ml` is the mirror
   reference where applicable; its `assume_coherent_matches` fail-open
   heuristic (eval.ml:20-22) is NOT inherited — undecidable matches are
   errors for closed terms (documented divergence, closed terms decide).
5. **Functions**: `DecD` clause evaluation — argument pattern matching,
   premise checking, first-match semantics mirroring the OCaml runtime's
   behavior; integer builtins for the wasm spec's abstract numerics enter
   ONLY through the D4 extension interface (a declared typeclass-style
   plugin), never the core.
6. **Relations**: derivability for `RelD` rules (substitution-instance +
   premises) with a bounded deterministic search procedure for execution
   (faithful-but-slow; the AL-style algorithmic compilation is explicitly
   NOT this arc). Wasm's `Step`/`Eval` relations drive execution.
7. **Differential harness**: a vendored OCaml wast driver (reusing the
   reference interpreter's parser from the pinned checkout) lowers each
   `.wast` to a neutral S-expr invocation script; `spectecil run-wast`
   executes invocations against the spec semantics; results diffed
   against the OCaml `--interpreter` on the same files. Per-assertion
   classification {pass | divergence(registered finding) |
   unsupported(declared class)}; tracked baseline
   `baselines/wast-differential.tsv` (result+id+class per assertion,
   golean format); `scripts/ci` gains the classified-set diff vs
   baseline. Re-pins only deliberate+explained.

## DONE (machine-checkable conjunction, all of it — `scripts/ci` enforced)

- [ ] ci GREEN including all arc-1 checks (round-trips stay byte-identical
      under the patched dump format, re-pinned).
- [ ] Dump losslessness: structural mixops/atoms round-trip; a ci probe
      distinguishes two mixops that collide under the old string encoding.
- [ ] Lean validator: 3/3 corpora green; ≥5 mutation probes rejected.
- [ ] Harness classifies **19,841/19,841** assertions across **97/97**
      files — zero unclassified, zero false passes (unsupported and
      divergence are explicit, counted classes).
- [ ] **Pass floor**: in the 20 integer/control files (i32, i64,
      int_exprs, int_literals, block, br, br_if, br_table, if, loop,
      return, call, local_get, local_set, local_tee, global, nop,
      unreachable, memory_grow, memory_size — ~2,400 assert_return/trap
      incl. float-typed cases), **every harness-classified non-float
      assert_return/assert_trap PASSES** (count reported, derived by the
      classifier, not hand-picked). Zero divergences in this set.
- [ ] Declared-unsupported classes are enumerated in the results section
      with counts (expected: float/SIMD numerics, assert_malformed
      [text/binary parsing = harness boundary], assert_exhaustion,
      others as discovered) — each with a one-line justification.
- [ ] 0 `partial def` / `sorry` / `native_decide` / heartbeat raises
      (existing hygiene grep) in `SpecTecLean/`.
- [ ] Mirror citations on every ported definition; divergences documented
      in-code; decision log current with [AGENT]/[USER] tags; checkpoint
      entries every ≤5 slices; results section written; audit ask posed.

## Hard boundaries

- No merge, no push, no gate weakening, no baseline re-pin without the
  reason committed alongside.
- No upstream bump; the ONLY deps/spectec change is the vendored D3/wast
  patch set under `patches/`, applied by script, diff-visible.
- Core stays language-agnostic (D4): wasm numerics live behind the
  extension interface; nothing wasm-specific in `SpecTecLean/` core
  namespaces.
- No AL/il2al port, no prose/latex work, no Go work in this arc.
- Park-don't-improvise: ambiguous OCaml behavior → mirror it or stop the
  slice and record; never approximate silently.

## Escape hatches (agent-declarable, each parks with a written record)

- If the D3 patch reveals further lossy encodings that make faithful
  semantics unreachable without larger upstream surgery: stop stage 1,
  record, re-scope with the user.
- If bounded relation search cannot decide the wasm `Step` relation in
  practical time even for the slow model: park stage 6/7 with
  measurements and a proposed alternative (e.g. premise-ordering hints),
  deliver stages 1-5 as the arc.
- If the wast driver boundary proves larger than "reuse the reference
  parser" (e.g. module instantiation semantics leak into the harness):
  record the boundary honestly and shrink the floor file list rather
  than blur the semantics/harness line.
- EMERGENCY EXIT always available (declare nature, park, report).

## Long-cycle provisions (CLAUDE.md)

Orchestrator scopes/verifies, workers execute in worktree lanes (ONE
WRITER PER WORKTREE; `SpecTecLean/` core + `baselines/` owned by one lane
at a time; docs/patches/harness-OCaml lanes may parallelize when
file-disjoint). Worker-claimed green is never accepted — the orchestrator
re-runs `scripts/ci`. Honesty conventions briefed into every worker:
verbatim outputs, derived tallies labeled, counts not adjectives, no
result claimed unseen. Decision log: docs/2026-08-20_arc2-log.md.

## Results (2026-08-21, EARLY EXIT via the stage-6/7 escape hatch)

**Exit invoked:** "If bounded relation search cannot decide the wasm
`Step` relation in practical time even for the slow model: park stage
6/7 with measurements and a proposed alternative, deliver stages 1-5 as
the arc." Delivered: stages 1-6 complete, plus a CORRECT but slow
stage-7 pilot (runner + driver + ci differential gate), plus — in a
post-exit continuation prompted by the goal monitor — the full-corpus
CLASSIFICATION (met with honest classes; see the scorecard). The one
remaining unmet DONE item is the 20-file pass floor, which is not met
and not claimed.

### DONE scorecard (line by line)

- ci GREEN incl. arc-1 checks: **MET** (last run 2026-08-21; includes
  the new wast pilot step).
- Dump losslessness + mixop-collision probe: **MET** (build-failing
  `#guard`s in SpecTecLean/Probes.lean; sha-pinned dumps).
- Validator 3/3 corpora + ≥5 mutation probes: **MET** (973/337/494 defs
  validate; 5/5 probes rejected).
- Harness classifies N/N across 97/97 files: **MET** (2026-08-21;
  numbers below are from the POST-AUDIT-FIX engine, arc2-fix — the
  audit found the earlier prose cited superseded totals and
  mischaracterized the error class; see docs/2026-08-21_arc2-audit.md
  finding 8): **20,029/20,029 assertions, zero unclassified, zero
  false passes** (baselines/wast-differential.tsv; scripts/
  wast-classify + wast-rollup, 120 s/file wall budget). Denominator is
  the harness's own metric — assertions parsed from the 97 driver
  command streams; the charter's 19,841 was a pre-arc estimate by an
  unstated count (textual `assert_` grep gives 19,984). Honest-classes
  statement: pass=90; fail=17 (cascades of earlier errored/skipped
  actions — none is a fresh decided mismatch); stuck=45; the dominant
  classes are error=11,502 — of which ~11.3k are ONE systematic engine
  gap, `entry call invoke: no clause applies`, occurring AFTER
  successful instantiation (NOT timeouts; arc-3a's first diagnostic
  target) — timeout=4,517 and resource=27 (wall/memory budget), and
  driver-boundary unsupported=3,831 across 7 classes. Pass counts are
  wall-budget-limited, not correctness-limited: vs the pre-fix engine,
  the flip matrix shows ZERO pass→fail flips; 13 stuck→pass (the
  trap-rule BLOCKER fix), 49 modules now honestly
  `unsupported:imports` (fail-closed linking; this converted
  ref_func's two FALSE passes and one mis-linked fail into visible
  errors), and the per-command slowdown (~1.7x, deriveCache soundness
  restriction + three-valued premise checking) moves the timeout
  boundary earlier (const.wast: row 738 → 422 within budget, pass
  152 → 47). The classification is complete and honest; it is NOT a
  claim of execution coverage.
- Pass floor (20 integer/control files): **NOT MET** (early exit).
- Declared-unsupported enumeration: **MET** — full-corpus per-class
  counts in baselines/wast-differential.tsv grand totals (post-fix):
  assert_return-pattern=2,000 (NaN patterns/vectors/null args),
  assert_malformed=1,073 (text/binary parsing = harness boundary),
  assert_invalid=580 (validation not executed; Module_ok is an assumed
  relation), assert_unlinkable=138, assert_trap-action=22,
  assert_exhaustion=11 (fuel semantics), assert_uninstantiable=7.
  (Counts grew vs the pre-fix sweep because fail-closed imports let
  more files finish inside the wall budget, so driver-boundary rows
  previously masked by `timeout` now count as themselves.) Module-level
  `unsupported:imports` (49 modules) is a runner boundary: no linker in
  the harness.
- Hygiene (0 partial/sorry/native_decide/heartbeat raises): **MET**
  (ci-enforced grep).
- Citations/divergence docs/log/results/audit ask: **MET** (this
  section; docs/findings/; docs/2026-08-20_arc2-log.md).

### What works (all through the real spec rules, no shortcuts)

`baselines/wast/mini.wast` end-to-end in ~0.9 s: module define →
`$instantiate` (allocmodule/alloctypes/allocfuncs chain incl. the
forward-guess premise order) → export lookup → `$invoke` →
`Step/ctxt-*`, `call_ref`, frame/label exits → assert_return PASS. This
is now a ci-gated differential baseline. nop.wast (89 commands, ~20
functions, table+elem): module decodes and instantiates within a larger
budget; its asserts do NOT pass within the sweep budget (baseline: 87
timeout) — an earlier draft of this sentence overstated this (audit
finding, docs/2026-08-21_arc2-audit.md #8).

### Measurements (the exit evidence)

- Steady-state `Step` derivation: ~1 s/step (26k reduceExp entries per
  step measured); first Step after instantiation ~27 s (cold caches).
- nop.wast instantiation: 218 s under the (incorrect) pre-deferral
  engine; >9 min with the correct ground-binding worklist. The full-file
  run was KILLED after 31 min still inside instantiation at 53 GB RSS
  (memory grows outside the now-bounded caches — symbolic intermediate
  terms during premise deferral are the suspect; machine safety on the
  shared host required the kill). No nop.rows result exists; none is
  claimed.
- Unbounded memo caches reached 8+ GB RSS on nop.wast (now epoch-flushed
  at fixed sizes).
- Extrapolation: 19,841 assertions × (seconds-to-minutes each) plus 97
  instantiations at minutes-to-hours each ≈ multi-day-to-week compute —
  not practical for a gate, and 2-3 orders of magnitude off.

Speedups already implemented (all semantics-preserving, in-code
citations): reduceExpCall memo (~50x), derive memo (kills the
exponential no-rule confirmation of split enumeration; LFP soundness
argument at the definition), Step-family anchor pruning, values-first
terminal shortcut, eqExp ptrEq short-circuit, CPS premise-aware
backtracking. The residual bottleneck is O(|store|) term traversal per
reduction/matching step — INHERENT to store-in-term rewriting over a
structurally-compared AST.

### Proposed alternatives (next-arc decision, recorded in TODO.md)

(a) hash-consed IL AST (O(1) eq/hash → real memoization; a pointer-memo
prototype benchmarked 20x in isolation but regressed in vivo — lead
logged, not claimed); (b) upstream-AL-style store indirection
(addresses + threaded store), trading against this arc's
execute-the-rules-directly fidelity bet; (c) the il2al/AL port (already
its own staging-plan item) with the rule-direct engine retained as the
semantic reference for the compiled path (the [USER] backlogged
compiled-vs-slow theorem).

### Findings shipped

docs/findings/: IterE-opt unwrapped reduction (eval.ml:314-321),
reduce_exp_call body substitution (eval.ml:531), $allocmodule
non-executable premise order (spec 4.4:103-143), eta_iter_exp assert
reachability. Plus the earlier candidates listed in TODO.md.

### Audit ask (unconditional)

This arc end requests the standard adversarial audit before any merge:
primary dimension OCaml↔Lean correspondence (mirror doctrine) over the
stage-7 engine additions — the engine-level rules (binding-eq
orientation + ground gate, worklist deferral, Steps closure, CPS input
matching, anchor pruning, derive/call memo soundness arguments) are
exactly where undocumented divergence risk concentrates; secondary
dimensions: gate integrity (ci step 7), record honesty (this section vs
the log), and the findings' accuracy against upstream sources. Merge and
sign-off are the user's.
