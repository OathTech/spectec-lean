import SpecTecLean.Al
import SpecTecLean.Il.Rel
import SpecTecLean.Il.ToSexpr
/-!
Wast-script runner (arc-2 stage 7): interprets the harness driver's
command stream against the spec's own execution semantics —
`$instantiate`/`$invoke` (4.4-execution.modules.spectec:183-215) evaluated
as spec functions, then the `Step` relation iterated to a value state
(the rule-direct engine, Il/Rel.lean).

Orchestration mirrors backend-interpreter/runner.ml at the spec level:
store threading, module registration (single current module — named
modules/registration are harness-unsupported classes), export lookup by
name, result comparison. Divergences from runner.ml (logged):
- assert_trap checks TRAP-ness only, not the message text.
- One current module instance (no Register/named-module table yet).

Every assertion classifies into pass / fail / trap-mismatch / stuck /
fuel / unsupported-<class> — nothing silent (charter DONE).
-/

namespace SpecTecLean.Il

namespace Runner

open Eval

/-- Strip subsumption wrappers (`SubE`) from a value expression head. -/
def stripSub : Exp → Exp
  | .mk (.subE e _ _) _ => stripSub e
  | e => e

/-- Case head name of a value expression, if any. -/
def headName (e : Exp) : Option String :=
  match (stripSub e).it with
  | .caseE op _ => AlDecode.caseName op
  | _ => none

/-- Record field access on a struct value. -/
def structField (e : Exp) (key : String) : Option Exp :=
  match (stripSub e).it with
  | .strE efs =>
    match efs.find? (fun f => match f with
      | .mk a _ => XlPrint.atomToString a == key) with
    | some (.mk _ v) => some v
    | none => none
  | _ => none

/-- Split a single-case notation value (`state`, `config`): payload
components. -/
def notationComps (e : Exp) : Option (List Exp) :=
  match (stripSub e).it with
  | .caseE _ p =>
    match p.it with
    | .tupE es => some es
    | _ => some [p]
  | _ => none

/-- The value-case head names of a variant type (e.g. `val`). -/
def variantHeads (env : Env) (fuel : Nat) (t : Typ) : EvalM (List String) := do
  match ← reduceTypdef env fuel t with
  | .variantT tcs =>
    pure (tcs.filterMap (fun c => match c with
      | .mk op _ _ _ => AlDecode.caseName op))
  | _ => err "variantHeads: not a variant"

/-- Empty store: every field of the `store` struct is an empty list. -/
def emptyStore (env : Env) (fuel : Nat) : EvalM Exp := do
  let t : Typ := .varT "store" []
  match ← reduceTypdef env fuel t with
  | .structT tfs => do
    let efs ← tfs.mapM (fun f => match f with
      | .mk atom tft _ _ =>
        pure (ExpField.mk atom (Exp.mk (.listE []) tft)))
    pure (.mk (.strE efs) t)
  | _ => err "store type is not a record"

inductive RunKind where
  | done (state : Exp) (results : List Exp)
  | trap (state : Exp)
  | stuck (cfg : Exp) (msg : String)
deriving Inhabited

/-- Iterate `Step` from a configuration to a terminal state. -/
def runConfig (env : Env) (fuel : Nat) (valHeads : List String) :
    Nat → Exp → EvalM RunKind
  | 0, cfg => pure (.stuck cfg "step budget exhausted")
  | steps+1, cfg => do
    -- values-first shortcut: a value/TRAP state needs no exhaustive
    -- no-rule confirmation (the search is exponential on failure)
    let terminal := match notationComps cfg with
      | some [_, instrsE] =>
        match (stripSub instrsE).it with
        | .listE instrs => instrs.all (fun i => match headName i with
            | some h => valHeads.contains h || h == "TRAP"
            | none => false)
        | _ => false
      | _ => false
    if terminal then
      match notationComps cfg with
      | some [state, instrsE] =>
        match (stripSub instrsE).it with
        | .listE instrs =>
          if instrs.any (fun i => headName i == some "TRAP") then
            pure (.trap state)
          else do
            let state ← reduceExp env fuel state
            pure (.done state (instrs.map stripSub))
        | _ => err "unreachable: terminal non-list"
      | _ => err "unreachable: terminal non-config"
    else do
    let (_, mixop, _, rules) ← match env.findRel? "Step" with
      | some d => pure d
      | none => err "relation Step not found"
    match ← Rel.derive env fuel [] [] "Step" mixop rules [cfg] 1 with
    | .ok [cfg'] => runConfig env fuel valHeads steps cfg'
    | .ok _ => err "Step produced unexpected arity"
    | .stuck m => pure (.stuck cfg m)
    | .noRule => do
      -- terminal analysis
      match notationComps cfg with
      | some [state, instrsE] =>
        match (stripSub instrsE).it with
        | .listE instrs =>
          let heads := instrs.map headName
          if heads.all (fun h => match h with
              | some h => valHeads.contains h
              | none => false) then do
            -- the state can still be symbolic (e.g. `(proj (call
            -- $allocmodule …))`): reduce before extraction
            let state ← reduceExp env fuel state
            pure (.done state (instrs.map stripSub))
          else if heads.any (fun h => h == some "TRAP") then
            pure (.trap state)
          else
            let bad := (instrs.find? (fun i => match headName i with
              | some h => !(valHeads.contains h) | none => true)).map
              (fun i => ((SpecTecLean.Sexpr.pp 0 1000000 (expToSexpr i)).2.take 240).toString)
            pure (.stuck cfg s!"no Step rule applies; first non-value instr: {bad.getD "?"}")
        | _ => pure (.stuck cfg "config instrs not a list")
      | _ =>
        pure (.stuck cfg s!"config shape unrecognized: {((SpecTecLean.Sexpr.pp 0 1000000 (expToSexpr cfg)).2.take 300).toString}")

/-- Evaluate a spec entry-point call (relation premises supported). -/
def evalCall (env : Env) (fuel : Nat) (f : Id) (args : List Exp)
    (retT : Typ) : EvalM Exp := do
  -- Module_ok/Externaddr_ok: assumed validation boundary (modules come
  -- from the reference parser; assert_invalid is an unsupported class)
  Rel.evalCallRel env fuel ["Module_ok", "Externaddr_ok"] f args retT

structure St where
  store : Exp
  modinst : Option Exp

/-- Extract (store, frame) from a `state` value. -/
def stateParts (state : Exp) : Option (Exp × Exp) :=
  match notationComps state with
  | some [s, f] => some (s, f)
  | _ => none

inductive Outcome where
  | pass
  | fail (detail : String)
  | unsupported (cls : String) (detail : String)
  | stuck (msg : String)
  | errorO (msg : String)
deriving Inhabited

def outcomeClass : Outcome → String
  | .pass => "pass"
  | .fail _ => "fail"
  | .unsupported c _ => s!"unsupported:{c}"
  | .stuck _ => "stuck"
  | .errorO _ => "error"

/-- Run an invoke action; returns results and the updated store. -/
def runInvoke (env : Env) (fuel steps : Nat) (valHeads : List String)
    (st : St) (name : String) (args : List AlValue) :
    EvalM (RunKind × List Exp) := do
  let mi ← match st.modinst with
    | some mi => pure mi
    | none => err "no module instantiated"
  let exports ← match structField mi "EXPORTS" with
    | some e => pure e
    | none => err "moduleinst has no EXPORTS"
  let nameE ← AlDecode.decode env fuel (.text name) (.varT "name" [])
  let exps ← match (stripSub exports).it with
    | .listE es => pure es
    | _ => err "EXPORTS not a list"
  let hit := exps.find? (fun xi =>
    match structField xi "NAME" with
    | some nm => eqExp nm nameE
    | none => false)
  let xi ← match hit with
    | some xi => pure xi
    | none => err s!"export {name} not found"
  let addr ← match structField xi "ADDR" with
    | some a => pure a
    | none => err "exportinst has no ADDR"
  let fa ← match (stripSub addr).it with
    | .caseE op p =>
      if AlDecode.caseName op == some "FUNC" then
        match p.it with
        | .tupE [a] => pure a
        | _ => err "FUNC addr payload shape"
      else err s!"export {name} is not a function"
    | _ => err "externaddr shape"
  let vals ← args.mapM (fun v => AlDecode.decode env fuel v (.varT "val" []))
  let valsE : Exp := .mk (.listE vals) (.iterT (.varT "val" []) .list)
  let cfg ← evalCall env fuel "invoke" [st.store, fa, valsE] (.varT "config" [])
  let rk ← runConfig env fuel valHeads steps cfg
  pure (rk, vals)

end Runner

end SpecTecLean.Il
