# Upstream note: `eta_iter_exp`'s `assert false` is reachable via unoriented binding equations

**Component:** `deps/spectec/spectec/src/il/eval.ml:935-943` (commit acc6e834)
**Found:** 2026-08-21, arc-2 stage 7
**Status:** note (unreachable in upstream's own usage); mirror diverges deliberately

`eta_iter_exp` ends in `assert false` for non-iteration types. Upstream
reaches `match_exp'`'s `_, IterE` row (eval.ml:876) only with oriented
`let`-style matching where the concrete side is iteration-typed, so the
assert never fires. Our engine executes raw-IL binding equations in
either orientation; a mismatched orientation can reach this case. The
mirror throws the engine's `Irred` instead (caught by the orientation
fallback); site comment at `SpecTecLean/Il/Eval.lean` (etaIterExp).
This is a latent robustness issue upstream only if `eval.ml` is ever
used for general execution.
