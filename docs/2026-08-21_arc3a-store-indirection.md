# Arc-3a store indirection: design + bisimilarity note (v1, 2026-08-21)

## Mechanism

A generic OPAQUE-VALUE facility (nothing wasm-specific, charter D4):
`Fresh.St.opaqueTab : Array Exp` holds immutable inline snapshots; a
handle `caseE %OPAQUE (numE gen)` (note = the value's type) stands for
`opaqueTab[gen]`. The runner wraps the initial store (Main run-wast);
handles then flow by ordinary substitution/binding. The engine
intercepts EXACTLY three reduction forms on handles (Eval.reduceExp,
marked in-code):

- `dotE handle atom` — project the field on the snapshot (O(1): strE
  field access returns the shared object);
- `updE/extE handle path v` — apply the path update to the snapshot via
  the ordinary reduce rows, mint a NEW handle (append-only generation);
- `compE` with either side a handle — compose on the snapshot(s), mint
  a new handle (the alloc chain builds stores with `++`).

## Bisimilarity-by-construction argument (the audit standard: can it
produce a WRONG answer, not just a different cost)

Invariant: `opaqueTab` entries are immutable; a handle's generation
uniquely determines its snapshot within a run.

1. Every intercepted operation returns EXACTLY what the ordinary reduce
   rows return on the inline snapshot — the interception fetches the
   snapshot and delegates to those very rows; only the (re)wrapping of
   the RESULT into a new handle differs, which is again governed by
   this argument inductively.
2. Every NON-intercepted structural observation of a handle FAILS
   CLOSED: the `%OPAQUE` atom cannot originate from a spec dump
   (spectec atom syntax has no '%'), so no reduce row rewrites it, no
   `matchExp'` row accepts it against any spec pattern (`eqMixop` false
   against every spec mixop; the caseE-vs-strE pair has no row), and
   variant/struct type inspection errors visibly. A handle-run can
   therefore differ from an inline-run only by getting VISIBLY STUCK
   where the inline run would proceed — never by answering differently.
3. Equality: `eqExp handle handle'` is structural = generation
   equality. Same generation ⇒ identical snapshot ⇒ sound TRUE.
   Different generations with EQUAL contents compare FALSE where the
   inline run would say TRUE — by (2)-style reasoning this can only
   fail a premise or miss a visited-guard cycle (bounded by fuel),
   i.e. stuck/slow, never a wrong answer. Var-binding of handles
   (`matchExp'` var row) does not inspect structure.
4. `isPureNormalExp handle` = true. The handle IS a normal value of the
   engine's extended value space; the represented snapshot is normal by
   the engine invariant that only reduced stores are wrapped (initial
   store built reduced; every subsequent generation is the output of
   the reduce rows).
5. `hasVarExp handle` = false, correctly: snapshots are ground by the
   same invariant (the ground-gate admitted them before wrapping).

Refinement summary: handle-run ⊑ inline-run ∪ {visible stuck}. Wrong
answers require a spec pattern or reduce row to MISREAD a handle, which
(2) excludes syntactically.

## Measurements (v1)

- 41-func module, i32.add invoke (probe p4): 16-24 s → 3.8 s (~5-6x).
- 1-func probes unchanged (~0.2-0.6 s end-to-end).
- Residual cost is frame-embedded moduleinst walks (O(#funcs) per
  step): funcinsts fetched from the store embed the INLINE moduleinst,
  which call_ref copies into each frame. v2 candidate: wrap moduleinst
  values; requires an interception story for their construction site
  (allocmodule's binding-eq) — under investigation.
