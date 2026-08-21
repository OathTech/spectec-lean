# Spec finding: `$allocmodule` premise order is not executable as written (forward guess)

**Component:** `deps/spectec/specification/wasm-3.0/4.4-execution.modules.spectec:103-143`
**Found:** 2026-08-21, arc-2 stage 7
**Status:** upstream-acknowledged (inline TODOs); engine accommodation documented here

## The behavior

`$allocmodule`'s premises use `moduleinst` (defined by the premise at
line 133) inside the earlier `$allocfuncs` premise (line 130). The
address list `fa*` is pre-computed by the "forward guess" premise
(line 122, upstream TODO: "get rid of this forward guess?"), which makes
a consistent order EXIST (122 → allocs → 132 → 133 → 130 as an equation
check), but the premises as *written* are not solvable left-to-right.

Upstream executes this via the il2al **animation** pass, which reorders
premises for executability before the AL interpreter runs them. Raw IL
(what we execute) keeps written order.

## Effect observed in our mirror before accommodation

Left-to-right execution reached line 130 with `moduleinst` free; generic
pattern matching happily bound `(s_7, fa*)` against a symbolic
`$allocfuncs` result, baking the free variable `moduleinst` into every
`funcinst.MODULE` in the store. Execution later got stuck at `CALL_REF`
(frame's `MODULE` field a free variable).

## Engine accommodation (semantics-preserving)

Two engine-level rules in `SpecTecLean/Il/Rel.lean` (checkPrems) and
`SpecTecLean/Il/Eval.lean` (reducePrems/reducePrem), both logged in-code:

1. **Worklist deferral**: an undecidable premise that still contains
   free variables is deferred and retried after later premises extend
   the substitution; rounds continue while progress is made. Equation
   order within a conjunction is semantically free, so only evaluation
   order changes (this is animation, done dynamically).
2. **Ground-solution gate**: a binding-equation match whose bindings
   still contain free variables is NOT accepted as a solution — it is
   deferred (prevents the free-`moduleinst` capture above).
