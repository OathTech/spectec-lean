# spectec-lean

Operating contract for this repo. Concise and always-loaded; amend it when a
practice proves its worth or its cost — keep it lean. Practices here are
adopted from the sibling projects (`../golean/CLAUDE.md`,
`../cerberus-lean-proj/CLAUDE.md`, `../ACL2Lean/CLAUDE.md`); when a rule here
is unclear, the sibling's fuller statement governs its intent.

**Goal.** (1) A Lean semantics for SpecTec — a deep embedding of SpecTec's IL
with an interpreter/semantics in Lean, replacing the OCaml runtime with an
all-Lean implementation that mirrors its structure. (2) Use it to define a
semantics for Go surface syntax, feeding the Go verifier in `../golean`.
Research materials and the architecture survey: `deps/README.md` (gitignored
reference checkouts — consult them instead of guessing; the OCaml sources in
`deps/spectec/spectec/src/` are the primary source for every porting question).

**Staging (decided 2026-08-20, in conversation with Mike — first arc charters
refine this):** (a) build the OCaml tool, dump elaborated IL via `backend-ast`
S-expressions; (b) IL AST + S-expr parser in Lean, round-trip the full Wasm
spec as the test corpus; (c) IL validation/semantics in Lean; (d) study the
`lean4-wip` generation backend; (e) prototype a small sequential Go core in
SpecTec EL early, to find where SpecTec's idioms fight Go. The OCaml frontend
(EL parsing/elaboration) stays a black-box elaborator until late; port it
last, if at all.

## Build & run (environment is fully repo-local)

```sh
source scripts/env.sh                 # repo-local opam root (.opam/) + switch (_opam/)
cd deps/spectec/spectec && make exe   # build ./spectec (OCaml 5.4.0)
./spectec ../specification/wasm-3.0/*.spectec --check          # elaborate (~8 s)
./spectec ../specification/wasm-3.0/*.spectec --ast -o out.sexpr    # IL S-expr dump
./spectec ../specification/wasm-3.0/*.spectec --interpreter t.wast  # meta-interpreter
```

`deps/spectec-lean4-wip/` is a worktree of the `lean4-wip` branch; its
`--lean4` target generates the (currently non-compiling, upstream-WIP)
`test-lean4/Wasm.lean`. Setup record + sandbox notes:
`docs/2026-08-20_ocaml-env-setup.md`. **Every `lake`/`lean` invocation goes
through `scripts/capped`** (cgroup cap; `SPECTEC_MEM_MAX` to override,
`=none` to opt out loudly) — `lean -M` and `prlimit` measured not to work.

## Machine-global state is forbidden

This machine runs several agents. Never modify global state (~/.gitconfig,
opam default switch, shell profiles, shared caches). Project-scoped only: the
OCaml side gets a **local opam switch** (`deps/spectec/_opam` or in-repo),
Lean toolchains via `lean-toolchain` + elan. Proposing a global change
requires explicit user approval at the moment of execution — never standing.

## Mirror-OCaml doctrine (adopted from cerberus-lean, load-bearing here)

When Lean code ports an OCaml component, **gratuitous logic divergence from
the OCaml is a defect as such** — no observed failure required. Every
divergence is either (a) eliminated by mirroring (with OCaml `file:line`
citations in a comment), or (b) documented in-code as deliberate, with
rationale (proof-friendliness and totality are legitimate reasons; the
backends differ in purpose). Undocumented divergence = finding. Upstream
`Wasm-DSL/spectec` is a moving target: `deps/README.md` records which commit
we mirror; bumping it is an explicit arc-level decision, never a side effect.

## The oracle and the gate

The OCaml spectec toolchain is the differential oracle: same input spec →
both implementations → diff the artifacts (IL dumps, interpreter results).
Wasm's own spec + test suite (`deps/wasm-spec/test/core/`) is the free,
authoritative corpus. Rules, from day one:

- **Guardrails first.** Before building a feature, pin its target behavior
  with differential cases. A feature is not "started" until its cases exist
  and classify correctly — a case we can't handle yet is visibly
  `unsupported`, never a false pass.
- **Fail closed, always.** Unknown IL nodes, unsupported constructs,
  malformed input → explicit error at the boundary. Never a silent
  approximation. Parsers hard-fail on unexpected input; no `| _ => none`
  default-swallowing. A visible red beats a hidden wrong answer.
- **One-command gate: `scripts/ci`.** Green before any checkpoint
  claim, audit, or merge. A green build is not evidence of correctness —
  the differential failing-set diff against a tracked baseline is the
  signal. Re-pin baselines only on a deliberate, explained coverage change,
  committed with the reason; never to launder a regression.
- **Never run a Lean build uncapped** — `scripts/capped` exists; use it for
  every `lake`/`lean` invocation (see Build & run). `#eval` a Bool before
  asking the kernel to decide it. Heartbeat/maxRecDepth raises are by
  definition defects:
  temporary, registered with an expected remover, or user-approved.

## Proof hygiene (when proofs start, from day one of them)

- Semantic-core definitions are **total** — no `partial`, no `sorry`, no
  `native_decide` (nor anything carrying `ofReduceBool`/`ofReduceNat`) in
  anything claimed done. `sorry` only as a called-out placeholder in
  acknowledged WIP.
- Adopt golean's in-build `Audit.lean` pattern: assert exact transitive
  axiom sets ({propext, Classical.choice, Quot.sound} + declared boundary
  axioms only), build-failing.
- **Non-vacuity:** a user-facing law ships in the same commit with a
  discharge witness on a concrete instance. No witness ⇒ it's a scaffold;
  its docstring says so.
- If two in-Lean artifacts must agree, that agreement is a **theorem, not a
  test**; opaque artifacts sit on a declared boundary list with an
  immovable-object justification (the OCaml oracle and the kernel itself
  are the permanent entries).

## Arc-based execution

- **Work is organized in arcs.** Each arc: a branch off `main`, a dated
  charter in `docs/` (`YYYY-MM-DD_<name>.md`), DRAFT until the user blesses
  it. The charter states scope, a machine-checkable DONE, and hard
  boundaries. An arc ends at branch-complete: gate green, record written,
  **audit ask posed** — merge and audit sign-off are the user's, always.
- **The repo is the record.** Every design decision, tradeoff, or open
  question goes in a tracked file (the arc charter, a dated note, TODO.md)
  — never left in chat. `TODO.md` is a backlog, not a journal; done items
  are deleted, narrative lives in charters.
- **Small slices, honest regressions.** One concern per commit, validated.
  Commit messages state what was verified.
- **Merge protocol, exactly** (the sibling protocol, unabridged): all work
  on branches — `main` only with direct user authorization for a specific
  commit; gate green; **the audit ask is unconditional** — the user may
  waive or trim, but the ask is never skipped; per-merge sign-off given at
  that moment for that merge; then `git checkout main && git merge
  --ff-only <branch>` (rebase + re-gate + re-ask if main moved; no merge
  commits, no pointer surgery); end parked on `main`; `git push` is a
  separate sign-off.
- **Audit practice:** the ACL2Lean five-step pattern (ground-truth first;
  parallel decorrelated adversarial reviewers, skeptical persona, primary
  sources; findings grounded to `file:line`; independent verification
  defaulting to refute; honest synthesis with self-spot-checks). Sign off
  on the audit **plan** (dimensions, agents, models, cost) before launching
  any subagent. Two-standard rule: adversarial review for semantics,
  claims, and records; deterrent standard ("catches the honest mistake?")
  for gates/lints — never harden gates against hypothetical adversaries.
  The primary audit dimension here is **OCaml↔Lean correspondence** (the
  mirror doctrine) and IL-semantics fidelity — always audit it; never
  skip a dimension because it has been green.
- **Model tiers** (2026-08 landscape; revisit on new releases, don't apply
  blindly): reviewers/verifiers Opus-class; delicate semantics/proof work
  Fable; mechanical batches Opus.

## Long-cycle / delegated work

- Any agent-proposed goal includes an **escape-hatch early-exit** the agent
  can declare; flag user-proposed goals lacking one before starting.
- Orchestrator scopes and verifies, workers do: exact file scope, validation
  commands, a park-don't-improvise rule. **Worker-claimed green is never
  accepted — re-run the gate independently.** Workers commit their own work,
  only on green, one coherent commit per slice.
- Long autonomous arcs additionally require: a self-contained counted DONE
  in one file; hard boundaries (no gate weakening, no trust-surface change,
  no merge/push); artifact-mediated continuity (status blocks, logs with
  judgment-call entries, ONE WRITER PER WORKTREE); honesty conventions
  briefed into every worker.
- **Quoted outputs are verbatim.** Anything formatted as tool output is the
  literal output; derived tallies are labeled derived. Report mechanically,
  not with adjectives — counts and file:line, not "faithful/complete".
  Never claim a build/test/axiom-check result without having run it and
  seen it; if something was skipped or failed, say so with the output.

## Housekeeping

- `deps/` and `.claude/` are gitignored. Date working notes
  `YYYY-MM-DD_name.md`; README/TODO/this file exempt.
- New `.lean` modules stay under ~1500 lines; new lemma families get their
  own module.
- Don't `rm -rf` scratch dirs without approval.
