# spectec-lean

A **generic SpecTec-in-Lean toolkit**: a deep embedding of [SpecTec]'s
intermediate language (IL) in Lean 4, with validation and a
faithful-but-slow executable semantics that mirror the OCaml toolchain,
differentially tested against it on the Wasm 3.0 specification. SpecTec
specs thereby get a Lean-native meaning.

**First client (planned):** a human-readable Go spec written in SpecTec,
and a frontend-soundness theorem `SpecTecSem(P) ≃ GoCoreSem(frontend(P))`
for the Go verifier in `../golean`. The toolkit stays language-agnostic —
Go (and Wasm numerics) enter only through declared extension points.
Objective and ratified decisions D1–D5:
`docs/2026-08-20_objective-go-frontend-soundness.md`.

[SpecTec]: https://github.com/Wasm-DSL/spectec

## Architecture

```
wasm-3.0 .spectec sources
        │  OCaml spectec (pinned + vendored patch: lossless structured dump)
        ▼
IL S-expression dump ──► SpecTecLean/Sexpr + Il/{Of,To}Sexpr (byte-identical round-trip)
                              │
                              ├─ Il/Valid     valid.ml mirror  (3 corpora green)
                              ├─ Il/Eval      eval.ml mirror   (fueled, total, fail-closed)
                              ├─ Il/Rel       rule-direct relation engine (no OCaml
                              │               counterpart: executes Step rules directly)
                              └─ Al + Runner  wast harness: OCaml driver emits AL-value
                                              command streams; Lean decodes, runs
                                              $instantiate/$invoke + Step to termination
```

The OCaml toolchain is the **differential oracle**: same spec in, both
implementations out, artifacts diffed. `scripts/ci` is the one-command
gate (pin check, sha-pinned dumps, capped build, hygiene grep,
round-trips, validator + mutation probes, fail-closed probes, wast
pilot baseline).

## Status (2026-08-21, arc 2 merged)

**Done and gated:**
- Lossless IL dump (vendored patch, `patches/`) round-trips
  byte-identically for wasm 1.0/2.0/3.0 (8.65 MB, 973 defs for 3.0).
- eval.ml + valid.ml fully mirrored (mirror doctrine: divergences are
  documented in-code or they're defects); all three corpora validate.
- Rule-direct execution works end-to-end on a pilot: define →
  instantiate → invoke → assert through the real spec rules, ci-gated.
- Full-corpus classification: **20,029/20,029 assertions across 97/97
  wast files** in explicit classes, zero unclassified, zero false
  passes (`baselines/wast-differential.tsv`). Honest headline: only 90
  pass within the per-file wall budget; ~11.3k hit one known
  engine gap (`invoke: no clause applies`), ~4.5k time out. The
  engine is *correct-but-slow* by design; throughput is arc 3a.
- Adversarial audit completed and all findings fixed
  (`docs/2026-08-21_arc2-audit.md`): 1 blocker, 7 majors, including
  two demonstrated wrong-answer paths — post-fix flip matrix shows
  zero pass→fail regressions.
- Four upstream bug reports drafted in `docs/findings/`.

**In flight (parallel worktree lanes):**
- **Arc 3a** (`docs/2026-08-21_arc3a-pass-floor.md`): make the
  rule-direct engine pass the 20 integer/control test files — fix the
  invoke gap, recover cache throughput, store representation, numerics
  extension.
- **Arc 3b** (`docs/2026-08-21_arc3b-il2al-stage1.md`): begin porting
  upstream's il2al compiler (IL → AL algorithms) + an AL interpreter —
  the future fast path. The rule-direct engine remains the
  spec-of-record; their agreement is slated to become a **theorem**
  (compiled-vs-slow, TODO.md), not a test.

## Build & run

Everything is repo-local (no global state — see CLAUDE.md):

```sh
source scripts/env.sh                 # repo-local opam root + switch
cd deps/spectec/spectec && make exe   # OCaml oracle (patched, pinned)
scripts/ci                            # the gate (green ≈ 4 min)
./.lake/build/bin/spectecil run-wast <dump.sexpr> <cmds>   # wast harness
scripts/wast-classify                 # full-corpus classification sweep
```

Every `lake`/`lean` invocation goes through `scripts/capped` (cgroup
memory cap). All work happens on branches — never on `main` — and lands
via audit + ff-only merge (CLAUDE.md, "Arc-based execution").

## Layout

| Path | What |
|---|---|
| `SpecTecLean/` | the Lean library (Sexpr, Xl, Il/*, Al, Runner) |
| `deps/` | gitignored: pinned OCaml spectec, wasm spec + test suite |
| `patches/` | vendored dump/driver patch against the pinned spectec |
| `baselines/` | sha pins, synthetic corpus, wast differential baseline |
| `scripts/` | ci, capped, env, worktree lanes, sweep tooling |
| `docs/` | charters, decision logs, audit records, findings |
| `TODO.md` | backlog (incl. the compiled-vs-slow theorem) |
