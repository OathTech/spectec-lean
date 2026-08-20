# Arc 1 — the IL bridge (charter)

Status: **BLESSED** (scope approved by Mike in conversation, 2026-08-20,
including the pretty-printer round-trip: "Add the PP too, let's do it
properly"). Branch: `arc1-il-bridge` (based on `setup-ocaml-env`, which is
awaiting its own merge decision; when that merges ff-only this branch is
automatically off `main`).

## Goal

Deep-embed SpecTec's IL in Lean and prove the embedding faithful by
round-tripping the OCaml toolchain's own IL dump of the full Wasm 3.0 spec —
**text → Sexpr → IL → Sexpr → text, byte-identical**. This pins the
OCaml↔Lean interchange for every later arc (validation, semantics) and gives
the project its first differential gate.

## Upstream pin

Mirroring `Wasm-DSL/spectec` @ `acc6e834ff403c82554d081237f327346190ad96`
(main, cloned 2026-08-20; recorded in `baselines/upstream-pins.txt`, checked
by `scripts/ci`). Bumping it is an arc-level decision, never a side effect.

## Scope (in order; one slice = one commit, validated)

1. **Charter + pins** (this file, `baselines/`).
2. **Lean project skeleton**: repo-root Lake project `SpecTecLean`, Lean
   v4.33.0, batteries v4.33.0 via the local mirror; builds through
   `scripts/capped` only.
3. **Sexpr layer** — `SpecTecLean/Sexpr.lean`: the S-expression datatype,
   text parser, and layout printer mirroring `util/sexpr.ml` (the `--ast`
   output format, width-80 boxing). Gate: text → Sexpr → text byte-identical
   on the full wasm-3.0 dump.
4. **IL AST** — `SpecTecLean/Il/Ast.lean` (+ `Xl.lean` for atoms / mixops /
   numerics), mirroring `src/il/ast.ml` and the `xl/` types it uses, with
   OCaml `file:line` citations per the mirror doctrine.
5. **IL reader/printer** — `SpecTecLean/Il/OfSexpr.lean` (Sexpr → IL,
   fail-closed: any unrecognized node is an explicit located error, never a
   skip) and `SpecTecLean/Il/ToSexpr.lean` (IL → Sexpr, mirroring
   `backend-ast/print.ml`). Gate: full-pipeline byte-identical round-trip.
6. **`scripts/ci` v1**: capped `lake build` + regenerate the wasm-3.0 IL
   dump with the pinned OCaml spectec + sha256 vs `baselines/` + the
   round-trip check. One command, fails loud.

## DONE (machine-checkable conjunction — all of it)

- [ ] `scripts/ci` exits 0, and it checks ALL of:
  - [ ] capped `lake build` of the whole project succeeds;
  - [ ] `deps/spectec` HEAD equals the pin in `baselines/upstream-pins.txt`;
  - [ ] the regenerated wasm-3.0 `--ast` dump's sha256 equals the pinned
        value (drift in either direction fails);
  - [ ] round-trip: `lake exe spectecil roundtrip <dump>` re-prints the
        dump **byte-identical** (empty `diff`), with **0** parse fallbacks
        (fail-closed errors abort, so success = 100% of nodes recognized).
- [ ] **0 `partial def`, 0 `sorry`, 0 `native_decide`** in `SpecTecLean/`
      (checked by `scripts/ci` mechanically, not by prose).
- [ ] Every type/constructor in the Lean IL AST carries an OCaml
      `file:line` citation; deliberate divergences (if any) documented
      in-code with rationale.
- [ ] Arc record appended to this file (results section), audit ask posed.

## Hard boundaries

- No merge, no push, no gate weakening, no baseline re-pin except with the
  reason committed alongside.
- No upstream `deps/spectec` bump.
- No semantics work (validation/evaluation) — parse/print fidelity only.
- Park-don't-improvise: if the dump contains a construct whose encoding is
  ambiguous or `print.ml` loses information needed to round-trip, STOP that
  slice and record the construct here rather than inventing an encoding.

## Escape hatch (agent-declarable)

If byte-identical layout proves intractable after faithfully mirroring
`util/sexpr.ml` (e.g. the boxing algorithm depends on OCaml `Format`
internals), fall back to: canonical-form byte equality (parse both sides to
Sexpr, print both with OUR printer, compare) **plus** structural Sexpr
equality against the original — recorded here as a deliberate, documented
divergence. If the IL AST turns out to be mid-refactor upstream such that
the dump doesn't correspond to `il/ast.ml` at the pin, stop and report.

## Results (2026-08-20, autonomous run — see docs/2026-08-20_arc1-log.md)

**DONE: all items green.** `scripts/ci` exits 0 and checks: upstream pin
(spectec @ acc6e834), regenerated wasm-3.0 IL dump sha256 vs baseline,
capped warning-free `lake build`, hygiene scan (0 `partial def`, 0 `sorry`,
0 `native_decide` — mechanically grepped), Sexpr-layer and full-pipeline
round-trips, and three fail-closed probes (unknown head / truncation /
non-canonical literal — all rejected, exit 1).

Headline numbers (all verified by running, 2026-08-20):

- wasm-3.0: 973 defs, 1,549,779 bytes — **byte-identical** full round-trip
  (text → Sexpr → IL → Sexpr → text), ~60 ms.
- Extra corpora beyond charter scope, same pinned commit: wasm-1.0
  (337 defs, 339,564 bytes) and wasm-2.0 (494 defs, 841,425 bytes) — both
  byte-identical; added to `scripts/ci` as roundtrip-only checks.

Modules: `SpecTecLean/Sexpr.lean` (layout mirror of util/sexpr.ml +
fail-closed parser), `SpecTecLean/OcamlEscape.lean` (String.escaped
mirror + canonical inverse), `SpecTecLean/Il/Ast.lean` (ast.ml mirror,
divergences documented in header), `SpecTecLean/Il/ToSexpr.lean`
(print.ml mirror), `SpecTecLean/Il/OfSexpr.lean` (fail-closed inverse
reader), `Main.lean` (`spectecil roundtrip[-sexpr]`).

**Open questions parked for later arcs** (also in the log):

1. **Structured mixops/atoms.** The dump's `Mixop.to_string` rendering is
   lossy (structure + arity erased, non-injective). IL validation/semantics
   will likely need the structure ⇒ either patch backend-ast upstream-style
   to dump mixops structurally (arc-level upstream decision) or prove
   string-tokens sufficient for the semantics' uses (mixop equality within
   one dump).
2. **LetPr binders** are dropped by the printer (print.ml:166) — same
   remedy if the semantics needs them.
3. Positions are absent from the dump; error reporting in later arcs will
   want them (upstream `--ast` flag addition, or live without).

Hard boundaries respected: no merge, no push, no upstream bump, no
semantics work. Audit ask: POSED (pre-merge adversarial audit — primary
dimension OCaml↔Lean correspondence per CLAUDE.md; user decides scope or
waiver).
