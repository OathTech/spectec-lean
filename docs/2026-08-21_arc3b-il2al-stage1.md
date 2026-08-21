# Arc 3b: il2al compiler port, stage 1 — DRAFT (awaiting blessing)

Branch: `arc3b-il2al-stage1` (off `main` after arc-2 lands). Lane is
GREENFIELD-ONLY: new modules under `SpecTecLean/Alir/` (AL AST,
translation, interpreter) + its own scratch tests. It does NOT touch
`SpecTecLean/Il/*`, `SpecTecLean/{Al,Runner}.lean`, `baselines/`, or
`scripts/ci` (core is arc-3a's lane; ci integration happens at landing,
serialized). A needed IL-layer change is a PARK-AND-REPORT to the
orchestrator, never an edit.

## Objective

Begin the compiled execution path: port upstream's il2al compiler
(IL → AL algorithms; this is how the OCaml toolchain actually runs the
20k-assert suite in minutes) and an AL interpreter, as the future
workhorse. The rule-direct engine remains the spec-of-record; the
long-term flagship is the compiled-vs-slow agreement THEOREM ([USER]
backlog item) — this arc lays its foundation and must not invert the
trust direction (no theorem hangs off the AL path).

## Scope (stage 1 of a multi-arc port)

1. **AL AST mirror** of `deps/spectec/spectec/src/al/ast.ml` (structs,
   instrs, exprs, paths — file:line citations, mirror doctrine).
2. **Translation mirror** of `il2al/translate.ml` + its helper passes
   (unified/animation as needed) for the EXECUTION fragment: Step-family
   rules and function defs; typing/validation algorithms excluded this
   stage.
3. **AL interpreter skeleton** executing the pure-instruction fragment
   (Step_pure-class algorithms): straight-line AL over an
   environment/stack model mirroring `backend-interpreter/interpreter.ml`
   shape (store not yet required for the pure fragment).
4. **Agreement harness (in-lane)**: pinned case set (≥20 pure-instr
   configurations) executed by BOTH the compiled path and the
   rule-direct engine (imported read-only), byte-compared; a case the AL
   path cannot run is visibly `unsupported`, never a false agree.
5. **Equivalence-theorem scaffold**: the agreement statement formalized
   for a TOY fragment (e.g. const/nop/drop) with a discharged concrete
   witness in the same commit (non-vacuity rule); its docstring says
   scaffold.

## DONE (machine-checkable)

- [ ] AL AST + translation compile the wasm-3.0 spec's execution
      fragment with zero errors; unsupported constructs REJECTED loudly
      at the boundary with counts (never silently dropped).
- [ ] AL interpreter runs the pure-instruction pinned case set;
      agreement harness: N/N cases agree with the rule-direct engine
      (N ≥ 20, enumerated in-repo).
- [ ] Toy-fragment equivalence theorem stated + witness discharged;
      axiom audit clean ({propext, Classical.choice, Quot.sound} +
      declared boundary axioms only).
- [ ] Lane-local gate script green (build + agreement + hygiene);
      0 partial/sorry/native_decide outside acknowledged-WIP markers
      listed in the results section.
- [ ] Mirror citations; decision log entries ([AGENT]/[USER]); results
      section; audit ask posed.

## Hard boundaries

- Greenfield modules only (see header). No merge/push. No upstream
  bump. No gate weakening of the main ci (this lane doesn't touch it).
- The rule-direct engine is read-only reference; no "fixing" it from
  this lane (park-and-report).
- Core stays language-agnostic; wasm specifics only via the same
  declared extension points.

## Escape hatches

- If translate.ml's fragment boundary explodes (the execution fragment
  drags in the whole middlend): park with a dependency map and a
  proposed smaller stage-1 fragment.
- If the AL interpreter cannot avoid the store for even the pure
  fragment: re-scope stage 1 to translation-only + printed-AL
  differential against upstream's `--print-al` output.
- EMERGENCY EXIT always available (declare nature, park, report).
