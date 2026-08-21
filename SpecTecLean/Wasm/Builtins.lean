import SpecTecLean.Il.Eval
/-!
Wasm-side native implementations of the spec's `hint(builtin)` functions
(D4 extension; registered by the harness via `Env.extCall` — nothing in
core namespaces knows about wasm). Each mirrors the OCaml reference
implementation in deps/spectec/spectec/src/backend-interpreter/
numerics.ml (cited per function) and the commented-out defining
equations in 3.1-numerics.scalar.spectec. Fail-closed: any argument
shape not exactly matched returns `none`, leaving the call residual
(visible downstream); no silent approximation.
-/

namespace SpecTecLean.Wasm.Builtins

open SpecTecLean.Il

/-- Truncation toward zero of a rational (numerics.ml:97-107
`Q.to_bigint`; spec equation commented at
3.1-numerics.scalar.spectec:78). Lean `Int.tdiv` is T-division (toward
zero); the reader enforces positive denominators. -/
private def trunczQ (num den : Int) : Option Int :=
  if den ≤ 0 then none else some (Int.tdiv num den)

private def numArg : Arg → Option Num
  | .expA (.mk (.numE nv) _) => some nv
  | _ => none

/-- The hook (register as `Env.extCall`). -/
def extCall (x : Id) (args : List Arg) (retT : Typ) : Option Exp :=
  match x, args with
  | "truncz", [a1] => do
    let nv ← numArg a1
    let i ← match nv with
      | .rat num den => trunczQ num den
      | .int i => some i
      | .nat n => some (Int.ofNat n)
      | _ => none
    pure (.mk (.numE (.int i)) retT)
  | "ceilz", [a1] => do
    -- ceil(n/d) with d>0 = -((-n).ediv d) (euclidean floor of the
    -- negation, negated)
    let nv ← numArg a1
    let i ← match nv with
      | .rat num den => if den ≤ 0 then none else some (-(Int.ediv (-num) den))
      | .int i => some i
      | .nat n => some (Int.ofNat n)
      | _ => none
    pure (.mk (.numE (.int i)) retT)
  | _, _ => none

end SpecTecLean.Wasm.Builtins
