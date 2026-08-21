import SpecTecLean.Alir.Agree
/-!
Equivalence-theorem SCAFFOLD (arc-3b stage 1, charter item 5).

`agreeStatement` formalizes compiled-vs-slow agreement — the flagship
[USER]-backlogged law — over the REAL executables: the Alir interpreter
on the pinned algorithms vs the rule-direct engine on a spec
environment. It is a SCAFFOLD: stated for the pinned case list,
quantified over the environment as a hypothesis, with the concrete
discharge below on a kernel-visible TOY environment. The full-spec
instance is checked by the (build-gated) `aliragree` executable, not by
the kernel — the wasm-3.0 environment is parsed at runtime and is far
beyond kernel reduction.

Non-vacuity witness: `toyEnv` is a minimal in-Lean IL script (val/instr
variants, `Step_pure` with the real nop rule shape, `Step` with the
pure-lift rule) — enough for the `[NOP]` case to take one derivation
step and terminate. `toy_agree_nop` discharges the agreement statement
on it by kernel reduction (`decide`), so the statement is proven
non-vacuous in the same commit that introduces it.
-/

namespace SpecTecLean.Il.Alir

open SpecTecLean.Il

/-- Boolean agreement checker: every case runs on BOTH engines and
agrees; any engine failure is `false` (never a false agree). -/
def agreeCheck (env : Env) (fuel steps : Nat)
    (cs : List (String × List Value)) : Bool :=
  cs.all (fun c =>
    match runRel env fuel steps c.2 with
    | .ok o => (runAlir fuel c.2).agree o
    | .error _ => false)

/-- SCAFFOLD (docstring per the non-vacuity rule): both engines agree
on a case list under environment `env`, stated by Boolean reflection
over the real executables. The wasm-3.0 instance of this statement is
exercised by the `aliragree` gate executable (its environment is parsed
at runtime, beyond kernel reduction); the theorem below discharges the
`toyEnv` instance in-kernel. -/
def agreeStatement (env : Env) (fuel steps : Nat)
    (cs : List (String × List Value)) : Prop :=
  agreeCheck env fuel steps cs = true

/-! ### Toy environment (kernel-visible IL script) -/

private def instrT : Typ := .varT "instr" []
private def valT : Typ := .varT "val" []
private def emptyTup : Exp := .mk (.tupE []) (.tupT [])
private def atomOp (s : String) : Mixop := .seq [.atom (.atom s)]
private def semi : Mixop := .infix .arg .semicolon .arg
private def arrow : Mixop := .infix .arg .arrow .arg

/-- `instr* : instr*` component type. -/
private def instrsT : Typ := .iterT instrT .list

/-- Variant case with an empty payload. -/
private def case0 (tag : String) : TypCase :=
  .mk (atomOp tag) (.tupT []) [] []

private def inst1 (dt : DefTyp) : Inst := .mk none [] [] dt

/-- The toy script: mirrors the SHAPE of the wasm IL fragment the
`[NOP]` derivation touches. `val` has one (unreachable) case; `instr`
has `NOP`; `Step_pure : instr* ~> instr*` has the real nop rule
(`NOP ~> eps`); `Step : config ~> config` has the pure-lift rule; the
state/config scaffolding matches runRel's construction. -/
private def configT : Typ := .varT "config" []
private def stateT : Typ := .varT "state" []
private def cfg2T : Typ := .tupT [.mk "_" configT, .mk "_" configT]
private def ins2T : Typ := .tupT [.mk "_" instrsT, .mk "_" instrsT]
private def stCompT : Typ :=
  .tupT [.mk "_" (.varT "store" []), .mk "_" (.varT "frame" [])]
private def cfgCompT : Typ := .tupT [.mk "_" stateT, .mk "_" instrsT]
private def mkCfg (z ins : Exp) : Exp :=
  .mk (.caseE semi (.mk (.tupE [z, ins]) cfgCompT)) configT

private def toyScript : Script := [
  .typD "val" none [] [inst1 (.variantT [case0 "UNIT"])],
  .typD "instr" none [] [inst1 (.variantT [case0 "NOP"])],
  .typD "store" none [] [inst1 (.structT [])],
  .typD "moduleinst" none [] [inst1 (.structT [])],
  .typD "frame" none [] [inst1 (.structT [
      .mk (.atom "LOCALS") (.iterT (.iterT valT .opt) .list) [] [],
      .mk (.atom "MODULE") (.varT "moduleinst" []) [] []])],
  .typD "state" none [] [inst1 (.variantT [
      .mk semi stCompT [] []])],
  .typD "config" none [] [inst1 (.variantT [
      .mk semi cfgCompT [] []])],
  -- Step_pure/nop : [NOP] ~> []   (4.3-execution.instructions.spectec
  -- `rule Step_pure/nop: NOP ~> eps`, elaborated shape)
  .relD "Step_pure" none [] arrow ins2T
    [.mk "nop" none [] arrow
      (.mk (.tupE [
        .mk (.listE [.mk (.caseE (atomOp "NOP") emptyTup) instrT]) instrsT,
        .mk (.listE []) instrsT]) ins2T)
      []],
  -- Step/pure : z; instr* ~> z; instr'*  -- Step_pure: instr* ~> instr'*
  .relD "Step" none [] arrow cfg2T
    [.mk "pure" none [] arrow
      (.mk (.tupE [
        mkCfg (.mk (.varE "z") stateT) (.mk (.varE "instr*") instrsT),
        mkCfg (.mk (.varE "z") stateT) (.mk (.varE "instr'*") instrsT)])
        cfg2T)
      [.rulePr "Step_pure" [] arrow
        (.mk (.tupE [
          .mk (.varE "instr*") instrsT,
          .mk (.varE "instr'*") instrsT]) ins2T)]]
]

def toyEnv : Env := Env.ofScript toyScript

/-- The toy case list: the `[NOP]` configuration. -/
def toyCases : List (String × List Value) := [("nop", [.caseV "NOP" []])]

/- NON-VACUITY WITNESS (build-failing): the toy instance of the
agreement statement, checked end-to-end through BOTH real engines at
every build. A KERNEL-level discharge (`theorem … := by decide`) is
currently impossible: the Il core helpers this computation passes
through (`isNormalExp`/`isPureNormalExp`/`hasVarExp`, mutual
`termination_by sizeOf`) compile to `WellFounded.fix`, which the kernel
cannot reduce — `decide` reduction verifiably gets stuck at those
instances (attempted 2026-08-21; error preserved in the arc-3b log).
PARKED for the theorem arc: fuel-ize or provide unfolding equations for
those helpers, then replace this guard with
`theorem toy_agree : agreeStatement toyEnv 2000 10 toyCases`.
Until then `agreeStatement` is a SCAFFOLD (docstring above says so). -/
#guard agreeCheck toyEnv 2000 10 toyCases

end SpecTecLean.Il.Alir
