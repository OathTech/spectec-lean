# Repo-local OCaml environment + spectec toolchain setup (2026-08-20)

Prepared ahead of the move into a restrictive sandbox. Everything is inside
the repo folder except elan toolchains (`~/.elan`, the accepted sibling
convention — additive installs only).

## What exists now

| Path | What |
|------|------|
| `.opam/` | repo-local opam ROOT (own package index + download cache; init'd `--bare -n --disable-sandboxing` — the outer sandbox provides isolation, and opam's bwrap cannot nest inside it) |
| `_opam/` | local switch: **ocaml-base-compiler.5.4.0**, dune 3.24.2, zarith 1.14, menhir 20260209, mdx |
| `scripts/env.sh` | `source` it: sets `OPAMROOT`/`OPAMSWITCH` + `opam env`, shell-scoped |
| `scripts/capped` | cgroup memory-cap wrapper for ALL `lake`/`lean` invocations (ported from golean; env vars `SPECTEC_MEM_MAX`, `SPECTEC_CAPPED`) |
| `deps/spectec/spectec/spectec` | built main-branch executable |
| `deps/spectec-lean4-wip/` | git worktree of the `lean4-wip` branch, its own built executable |

Lean toolchains installed in elan: v4.25.0-rc1 (pinned by lean4-wip's
`test-lean4/lean-toolchain`) plus 4.26.0–4.33.0 already present.

## Verified working (all run 2026-08-20, exit 0 unless noted)

Main branch (`deps/spectec/spectec`, after `source scripts/env.sh`):

- `make exe` — builds `./spectec` (vendors the reference interpreter in).
- `./spectec ../specification/wasm-3.0/*.spectec --check` — full Wasm 3.0
  spec elaborates in ~8.3 s.
- `--ast -o` — S-expression IL dump: 65,600 lines / 1.5 MB for wasm-3.0.
  **This is the planned OCaml→Lean bridge format** (see CLAUDE.md staging).
- `--interpreter test-interpreter/sample.wast` — meta-interpreter runs the
  spec-derived AL semantics: prints `- print_i32: 10`.
- `--latex -o` (12,662-line .tex; no pdflatex on this machine — rendering
  to PDF unavailable, generation fine), `--prose -o` (6,784 lines),
  `--print-il` (11,832 lines).

lean4-wip worktree (`deps/spectec-lean4-wip/spectec`):

- `make exe` builds; `./spectec ../specification/wasm-3.0/*.spectec --lean4 -o`
  generates an 11,289-line Lean file.
- **Provenance finding:** the checked-in `test-lean4/Wasm.lean` (10,790
  lines) IS the output of `backend-lean4/print.ml` (`--lean4`), not a
  hand/agent translation: regenerated vs checked-in differ in 438 lines
  modulo source-position path comments, all consistent with the spec
  having advanced since it was last regenerated. The printer's emitted
  preamble contains the hand-coded helper defs (marked so in print.ml).
- The checked-in `Wasm.lean` does NOT compile under its pinned
  v4.25.0-rc1: 2 × `error: Missing cases` (lines 66, 244) — an upstream
  printer gap, consistent with the branch name. Reference material for
  the generation route, not a working artifact, and NOT the project
  deliverable (the project builds a SpecTec interpreter/semantics in
  Lean; per-spec generation is a complementary route to study).

## Offline / sandbox readiness

- Works with no network: everything above (opam switch fully built;
  `dune build` needs nothing external; elan toolchains installed).
- **Lake deps offline (verified 2026-08-20):** bare mirrors in
  `deps/mirrors/` (batteries, iris-lean) + insteadOf redirects in
  `scripts/gitconfig`, active via `GIT_CONFIG_GLOBAL` (exported by
  `scripts/env.sh`; includes `~/.gitconfig` back for identity). Smoke
  test passed: scratch Lake project on leanprover/lean4:v4.33.0
  requiring `batteries @ v4.33.0` built green through `scripts/capped`;
  redirect PROVEN active (mirror moved aside → fetch fails on the local
  path, no network fallback). batteries release tags track Lean
  versions; v4.33.0 is the newest matching an installed toolchain.
- Needs network (do before entering the sandbox, or not at all):
  `opam install` of NEW packages (root's download-cache covers only what
  was installed), `elan toolchain install` of new versions, NEW Lake
  deps beyond the mirrored two (notably mathlib, whose olean cache also
  needs Reservoir — out of scope unless decided), git fetches/pushes in
  `deps/` or upstream bumps (arc-level decisions), the two
  browser-only ACM papers listed in `deps/README.md`.
- opam switch/root config is repo-local, so even switch-level operations
  work in-sandbox provided the sandbox grants the repo folder.
