import SpecTecLean.Alir.Interp
/-!
Pinned pure-instruction AL algorithms — HAND-MIRRORED from the oracle's
own `--print-al` output (docs/2026-08-21_arc3b-pinned-al.txt; generated
from the pinned spectec @ acc6e834 + vendored patches on wasm-3.0).
These stand in for compiled translator output until the translator arc
lands (see the arc-3b log's escape-hatch entry); each algorithm cites
its printed text verbatim.

Expression NOTES are placeholders (`(varT "_" [])`): the stage-1
interpreter consults notes nowhere (upstream consults them only in
AppendI and CvtE assignment, both outside the fragment); the printed AL
text does not carry types. Documented divergence.
-/

namespace SpecTecLean.Il.Alir

open SpecTecLean.Il

private def noT : Typ := .varT "_" []
private def e (it : Expr') : Expr := .mk it noT
private def opOf (tag : String) : Mixop := .seq [.atom (.atom tag)]

/-- `Step_pure/unreachable { Trap }` -/
def algoUnreachable : List Arg × List Instr :=
  ([], [.trapI])

/-- `Step_pure/nop { Nop }` -/
def algoNop : List Arg × List Instr :=
  ([], [.nopI])

/-- ```
Step_pure/drop {
 Assert (top_value())
 Pop val
}
``` -/
def algoDrop : List Arg × List Instr :=
  ([], [
    .assertI (e (.topValueE none)),
    .popI (e (.varE "val"))
  ])

/-- ```
Step_pure/select t*{t <- t*}?{t* <- t*?} {
 Assert (top_value(I32))
 Pop (I32.CONST c)
 Assert (top_value())
 Pop val_2
 Assert (top_value())
 Pop val_1
 If ((c =/= 0)) { Push val_1 } Else { Push val_2 }
}
```
The parameter is the nested option-of-list iteration
`t*{t <- t*}?{t* <- t*?}`; the pop pattern `(I32.CONST c)` is the CONST
case with the I32 numtype as first argument (printed dotted by the AL
printer). -/
def algoSelect : List Arg × List Instr :=
  ([.expA (e (.iterE
      (e (.iterE (e (.varE "t")) (.mk .list [("t", e (.varE "t*"))])))
      (.mk .opt [("t*", e (.varE "t*?"))])))],
   [
    .assertI (e (.topValueE (some (e (.caseE (opOf "I32") []))))),
    .popI (e (.caseE (opOf "CONST")
      [e (.caseE (opOf "I32") []), e (.varE "c")])),
    .assertI (e (.topValueE none)),
    .popI (e (.varE "val_2")),
    .assertI (e (.topValueE none)),
    .popI (e (.varE "val_1")),
    .ifI (e (.binE .ne (e (.varE "c")) (e (.numE (.nat 0)))))
      [.pushI (e (.varE "val_1"))]
      [.pushI (e (.varE "val_2"))]
  ])

/-- Stage-1 algorithm table (keys = instruction tags, the dispatch
convention of ds.ml lookup_algo / interpreter.ml create_context). -/
def pureAlgos : Algos := [
  ("UNREACHABLE", algoUnreachable),
  ("NOP", algoNop),
  ("DROP", algoDrop),
  ("SELECT", algoSelect)
]

end SpecTecLean.Il.Alir
