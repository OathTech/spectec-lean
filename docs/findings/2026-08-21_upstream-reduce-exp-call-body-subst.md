# Upstream finding: `reduce_exp_call` substitutes clause bodies with argument bindings only

**Component:** `deps/spectec/spectec/src/il/eval.ml:511-531` (commit acc6e834)
**Found:** 2026-08-20, arc-2 stage 7 (running `$instantiate` as a spec function)
**Status:** candidate upstream report; our mirror diverges by necessity (documented)

## The behavior

`reduce_exp_call` matches the call's arguments against the clause
patterns (producing substitution `s`), then checks the clause premises
with `reduce_prems env s prems` — but on success substitutes the clause
body with **`s` alone** (eval.ml:531). Bindings introduced by the
premises themselves (`-- if x = $f(…)` binding equations / `let`
premises) never reach the body.

For clauses in the wasm-3.0 spec whose *result* is premise-bound — e.g.
`$instantiate` (body references `s'`, `f`, `instr*` all bound by
premises), all `$alloc*` functions — the substituted body retains free
variables and the "reduced" call is wrong (or irreducible downstream).

## Why upstream doesn't see it

The middlend only evaluates simple, premise-light functions; functions
like `$instantiate` are executed via il2al/AL, not `eval.ml`.

## Mirror handling

`SpecTecLean/Il/Eval.lean` `reducePrems` returns the accumulated
substitution (`PremRes.yes s''`) and `reduceExpCall` substitutes the
body with it (divergence note at the definition).
