# Upstream finding: `reduce_exp` IterE-Opt all-some case returns an ill-typed, unwrapped result

**Component:** `deps/spectec/spectec/src/il/eval.ml:314-321` (commit acc6e834)
**Found:** 2026-08-21, arc-2 stage 7 (Lean mirror execution of wasm-3.0 instantiation)
**Status:** candidate upstream report; our mirror carries a documented deliberate divergence

## The behavior

`reduce_exp` on `IterE (e1, (Opt, xes))` when every iteration-domain value
is `Some`:

```ocaml
else if List.for_all Option.is_some eos' then
  let es1' = List.map Option.get eos' in
  let s = List.fold_left2 Subst.add_varid Subst.empty ids es1' in
  reduce_exp env (Subst.subst_exp s e1')     (* <- returned BARE *)
```

The result is the substituted body — **element-typed**, where the `IterE`
node itself is opt-typed (`t?`). The `None` branch by contrast correctly
produces `OptE None $> e`. So reducing e.g. the constructor pattern
`SUB fin? y* ct` with `fin? := OptE (Some FINAL)` yields a `SUB` value
whose first component is a bare `FINAL` (typed `final`) in a position
typed `final?`.

## Why upstream doesn't see it

`eval.ml` is exercised by the middlend on static, mostly-type-level
terms; value construction at runtime goes through il2al + the AL
interpreter, which never calls this code path. Downstream consumers that
would break on the unwrapped form:

- `match_exp'` against an opt-iteration pattern: the `OptE`-selective rows
  (eval.ml:830-874) don't fire; control reaches `eta_iter_exp`
  (eval.ml:876-878) whose non-iter case is `assert false` (eval.ml:943).
- `TheE` reduction (`as_opt_exp`) expects an `OptE`.

## Observed effect in our mirror

wasm-3.0 `$subst_subtype` clause matching failed for every concrete
`SUB` value during `$instantiate` (all clauses fall through), cascading
into fully symbolic `$alloctypes`/`Expand` results. Mirror fix
(documented divergence at `SpecTecLean/Il/Eval.lean`, IterE `.opt`
all-some row): wrap the substituted body in `OptE (Some …)`, keeping the
value type-correct. All downstream matching then proceeds.

## Suggested upstream fix

```ocaml
OptE (Some (reduce_exp env (Subst.subst_exp s e1'))) $> e
```
