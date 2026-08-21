import SpecTecLean.Alir.Algos
import SpecTecLean.Al
import SpecTecLean.Runner
/-!
Agreement harness (arc-3b stage 1, charter item 4): the SAME pinned
pure-instruction configurations executed by BOTH the AL interpreter
(Alir, on the oracle-pinned algorithms) and the rule-direct engine
(Il/Rel, on the real wasm-3.0 spec dump), outcomes compared. A case
either engine cannot run is a visible `unsupported`/`error` verdict —
never a false agree.

THIS FILE IS THE PINNED CASE LIST (charter: tracked in-lane). 24 cases.

Boundary converters are harness code, total and fail-closed:
- `toAlValue` : Alir.Value → AlValue feeds the existing type-directed
  decoder (SpecTecLean/Al.lean, read-only import) so the IL side gets
  correctly-typed value exps without hand-building notes.
- `ofIlValue` : IL value exp → Alir.Value projects the rule-direct
  engine's terminal values for comparison (derived BEq on the Value
  mirror; tags via the same atom printer both engines use).
-/

namespace SpecTecLean.Il.Alir

open SpecTecLean.Il

/-- Alir value → AL harness value (value fragment only; FnameV has no
AlValue counterpart and fails closed). -/
def toAlValue (fuel : Nat) (v : Value) : Except String AlValue :=
  match fuel with
  | 0 => .error "toAlValue: fuel"
  | n+1 =>
    match v with
    | .numV nu => .ok (.num nu)
    | .boolV b => .ok (.bool b)
    | .textV s => .ok (.text s)
    | .listV vs => do .ok (.list (← vs.attach.mapM
        (fun ⟨v1, _⟩ => toAlValue n v1)))
    | .strV fs => do .ok (.str (← fs.attach.mapM
        (fun ⟨(k, v1), _⟩ => do pure (k, ← toAlValue n v1))))
    | .caseV tag args => do .ok (.case tag (← args.attach.mapM
        (fun ⟨v1, _⟩ => toAlValue n v1)))
    | .optV none => .ok (.opt none)
    | .optV (some v1) => do .ok (.opt (some (← toAlValue n v1)))
    | .tupV vs => do .ok (.tup (← vs.attach.mapM
        (fun ⟨v1, _⟩ => toAlValue n v1)))
    | .fnameV f => .error s!"toAlValue: FnameV {f} outside value fragment"

/-- IL value exp → Alir value (projection for comparison; subsumption
wrappers stripped as in Runner.stripSub; fail-closed outside the value
fragment). -/
def ofIlValue (fuel : Nat) (v : Exp) : Except String Value :=
  match fuel with
  | 0 => .error "ofIlValue: fuel"
  | n+1 =>
    match (Runner.stripSub v).it with
    | .numE nu => .ok (.numV nu)
    | .boolE b => .ok (.boolV b)
    | .textE s => .ok (.textV s)
    | .listE es => do .ok (.listV (← es.attach.mapM
        (fun ⟨e1, _⟩ => ofIlValue n e1)))
    | .optE none => .ok (.optV none)
    | .optE (some e1) => do .ok (.optV (some (← ofIlValue n e1)))
    | .tupE es => do .ok (.tupV (← es.attach.mapM
        (fun ⟨e1, _⟩ => ofIlValue n e1)))
    | .strE fs => do .ok (.strV (← fs.attach.mapM
        (fun ⟨f, _⟩ => match f with
          | .mk a e1 => do pure (atomName a, ← ofIlValue n e1))))
    | .caseE op p => do
      let args ← match p.it with
        | .tupE es => es.attach.mapM (fun ⟨e1, _⟩ => ofIlValue n e1)
        | _ => do pure [← ofIlValue n p]
      -- anonymous singleton wrapper cases (literal-notation types like
      -- the CONST payload family) project to their payload: upstream's
      -- AL values carry the bare literal — construct.ml's al_of_num,
      -- observable in the driver output `(C "CONST" (C "I32") (N 1))`.
      -- Multi-argument anonymous cases (e.g. globaltype) keep CaseV "",
      -- construct.ml:1202.
      match mixopTag op, args with
      | "", [single] => .ok single
      | tag, _ => .ok (.caseV tag args)
    | _ => .error "ofIlValue: outside value fragment"

/-- Common outcome for both engines. -/
inductive Outcome where
  | done (stack : List Value)   -- terminal, bottom-first values
  | trap
  | other (side msg : String)   -- visible can't-run/stuck/error
deriving Repr, BEq, Inhabited

def Outcome.agree : Outcome → Outcome → Bool
  | .done a, .done b => a == b
  | .trap, .trap => true
  | _, _ => false

/-- AL side: run the instruction sequence through the Alir interpreter
on the pinned algorithms. -/
def runAlir (fuel : Nat) (instrs : List Value) : Outcome :=
  match runSeq pureAlgos fuel instrs with
  | .ok stack => .done stack
  | .error .trap => .trap
  | .error .fail => .other "alir" "fail"
  | .error (.error m) => .other "alir" m
  | .error .fuel => .other "alir" "fuel"

/-- Empty struct value for a named struct type: every field an empty
list (generalization of Runner.emptyStore, which is store-specific;
read-only reuse impossible without editing Runner — harness-local). The
pure-instruction Step rules never inspect the frame/module contents, so
list-shaped placeholders in non-list fields are unreachable (documented
harness approximation; a rule that DID inspect them would surface as a
visible stuck/error, never a false agree). -/
def emptyStructVal (env : Env) (fuel : Nat) (name : String) :
    EvalM Exp := do
  let t : Typ := .varT name []
  match ← Eval.reduceTypdef env fuel t with
  | .structT tfs => do
    let efs ← tfs.mapM (fun f => match f with
      | .mk atom tft _ _ =>
        pure (ExpField.mk atom (Exp.mk (.listE []) tft)))
    pure (.mk (.strE efs) t)
  | _ => Eval.err s!"{name} type is not a record"

/-- Rule-direct side: decode the same case values into typed IL instr
exps, wrap them in a minimal config `((store; frame); instr*)` (empty
store, empty frame — pure rules never read them), and reuse
Runner.runConfig — the SAME terminal analysis the arc-2 harness uses —
iterating the full `Step` relation (sequence decomposition lives in
Step/ctxt-instrs, not in Step_pure). -/
def runRel (env : Env) (fuel steps : Nat) (instrs : List Value) :
    Except String Outcome := do
  let avs ← instrs.mapM (toAlValue fuel)
  let instrT : Typ := .varT "instr" []
  let semi : Mixop := .infix .arg .semicolon .arg
  let (rk, _) ← ((do
      let es ← avs.mapM (fun v => AlDecode.decode env fuel v instrT)
      let valHeads ← Runner.variantHeads env fuel (.varT "val" [])
      let store ← Runner.emptyStore env fuel
      let modinst ← emptyStructVal env fuel "moduleinst"
      let frameT : Typ := .varT "frame" []
      let frame : Exp := .mk (.strE [
        .mk (.atom "LOCALS")
          (.mk (.listE []) (.iterT (.iterT (.varT "val" []) .opt) .list)),
        .mk (.atom "MODULE") modinst]) frameT
      let state : Exp := .mk
        (.caseE semi (.mk (.tupE [store, frame])
          (.tupT [.mk "_" (.varT "store" []), .mk "_" frameT])))
        (.varT "state" [])
      let ins : Exp := .mk (.listE es) (.iterT instrT .list)
      let cfg : Exp := .mk
        (.caseE semi (.mk (.tupE [state, ins])
          (.tupT [.mk "_" (.varT "state" []),
                  .mk "_" (.iterT instrT .list)])))
        (.varT "config" [])
      Runner.runConfig env fuel valHeads steps cfg) :
      EvalM Runner.RunKind).run {}
    |>.mapError (fun e => s!"rel: {reprStr e}")
  match rk with
  | .trap _ => pure .trap
  | .done _ results => do
    let vs ← results.mapM (ofIlValue fuel)
    pure (.done vs)
  | .stuck _ m => pure (.other "rel" s!"stuck: {m}")

/-- Shorthands for case construction. -/
private def i32const (n : Nat) : Value :=
  .caseV "CONST" [.caseV "I32" [], .numV (.nat n)]
private def i64const (n : Nat) : Value :=
  .caseV "CONST" [.caseV "I64" [], .numV (.nat n)]
private def nop : Value := .caseV "NOP" []
private def drop : Value := .caseV "DROP" []
private def unreachable : Value := .caseV "UNREACHABLE" []
private def select : Value := .caseV "SELECT" [.optV none]

/-- THE PINNED CASE LIST (24 cases; instruction sequences, values as
leading CONST instrs — stack top is the rightmost value). -/
def cases : List (String × List Value) := [
  ("nop-empty",            [nop]),
  ("nop-one-val",          [i32const 7, nop]),
  ("nop-two-vals",         [i32const 1, i64const 2, nop]),
  ("nop-nop",              [nop, nop]),
  ("drop-i32",             [i32const 42, drop]),
  ("drop-i64",             [i64const 9, drop]),
  ("drop-top-of-two",      [i32const 1, i32const 2, drop]),
  ("drop-after-nop",       [i32const 5, nop, drop]),
  ("double-drop",          [i32const 1, i32const 2, drop, drop]),
  ("unreachable",          [unreachable]),
  ("unreachable-with-val", [i32const 3, unreachable]),
  ("unreachable-two-vals", [i32const 3, i64const 4, unreachable]),
  ("nop-then-unreachable", [nop, unreachable]),
  ("select-true",          [i32const 10, i32const 20, i32const 1, select]),
  ("select-false",         [i32const 10, i32const 20, i32const 0, select]),
  ("select-true-i64",      [i64const 11, i64const 22, i32const 5, select]),
  ("select-false-keep",    [i32const 9, i32const 10, i32const 20, i32const 0, select]),
  ("select-then-drop",     [i32const 1, i32const 2, i32const 1, select, drop]),
  ("select-then-nop",      [i32const 1, i32const 2, i32const 0, select, nop]),
  ("drop-then-select",     [i32const 1, i32const 2, i32const 3, i32const 1, drop, select]),
  ("two-selects",          [i32const 1, i32const 2, i32const 1, select,
                            i32const 4, i32const 0, select]),
  ("select-unreachable",   [i32const 1, i32const 2, i32const 1, select, unreachable]),
  ("vals-only",            [i32const 1, i64const 2]),
  ("empty-seq",            [])
]

/-- Run all pinned cases; returns per-case rows
(name, alir outcome, rel outcome, verdict). -/
def runAll (env : Env) (fuel steps : Nat) :
    List (String × String × String × String) :=
  cases.map (fun (name, instrs) =>
    let a := runAlir fuel instrs
    let r := match runRel env fuel steps instrs with
      | .ok o => o
      | .error m => .other "rel" m
    let verdict := match a, r with
      | .other s m, _ | _, .other s m => s!"UNSUPPORTED({s}: {m})"
      | _, _ => if a.agree r then "AGREE" else "DISAGREE"
    (name, reprStr a, reprStr r, verdict))

end SpecTecLean.Il.Alir
