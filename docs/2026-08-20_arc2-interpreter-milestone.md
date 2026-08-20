# Arc 2 — the interpreter milestone (charter)

Status: **DRAFT** (awaiting Mike's blessing). Branch:
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

## Results

(to be written at arc end)
