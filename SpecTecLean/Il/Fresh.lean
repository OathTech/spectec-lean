import SpecTecLean.Il.Ast
import Std.Data.HashMap
/-!
Fresh identifier generation, mirroring `deps/spectec/spectec/src/il/fresh.ml`.

Deliberate divergence (logged, arc-2): fresh.ml uses PROCESS-GLOBAL mutable
counter maps (fresh.ml:5-8) — one counter per base name per id-space,
monotonic for the whole OCaml run. Here the counters are an explicit
`Fresh.St` value threaded through `FreshM` (a `StateM`): behavior is
identical relative to a counter state, but absolute name choices can
differ from an OCaml run whose call history differs. Substituted terms are
never byte-compared against oracle output (only unmodified dumps are), so
this is alpha-variance only.
-/

namespace SpecTecLean.Il.Fresh

/-- Cache payload for `Rel.derive` results (defined here to avoid an
import cycle; Rel converts to/from its `DeriveRes`). -/
inductive DeriveResC where
  | ok (outputs : List Exp)
  | noRule
  | stuck (msg : String)
deriving Inhabited

/-- One counter map per id-space (fresh.ml:5-8). Association list keyed by
base name (small; deterministic). -/
structure St where
  typids : List (String × Nat) := []
  varids : List (String × Nat) := []
  defids : List (String × Nat) := []
  gramids : List (String × Nat) := []
  /-- Scratch flag: set by the checkPrems→CPS adapter in Rel.deriveCore
  when a rule's premises were UNDECIDABLE (three-valued result squeezed
  through the Option-typed split-enumeration plumbing). deriveCore
  saves/resets/reads/restores it around each rule attempt; no other
  reader. -/
  premsUnknown : Bool := false
  /-- Memo table for `Eval.reduceExpCall` (PERF, semantics-preserving:
  spec functions are pure and reduction deterministic, so caching
  (defid, reduced args) → result changes cost only; `.fuel` throws
  propagate before insertion, so no fuel-truncated result is cached). -/
  callCache : Std.HashMap (String × List Arg) (Option Exp) := {}
  /-- Memo for `Rel.derive` (relation, inputs) → result. SOUND: derive
  is deterministic, and visited-guard refusals prune only cyclic
  derivations, which can never be required (least fixed point admits
  cycle-free trees), so the result is independent of the visited set. -/
  deriveCache : Std.HashMap (String × List Exp) DeriveResC := {}
deriving Inhabited

/-- Monad-polymorphic so callers can layer errors (e.g. Subst's
`StateT St (Except String)`). -/
abbrev FreshM := StateM St

private def bump (m : List (String × Nat)) (s : String) :
    Nat × List (String × Nat) :=
  match m.lookup s with
  | none => (1, (s, 1) :: m)
  | some i => (i + 1, (s, i + 1) :: m.filter (fun p => p.1 != s))

/-- fresh.ml:10-18 `fresh_id`: `"_"` is never renamed; otherwise
`s#<counter>`. -/
private def freshId [Monad m] (proj : St → List (String × Nat))
    (upd : St → List (String × Nat) → St) (s : String) : StateT St m String := do
  if s == "_" then return s
  let st ← get
  let (i, m) := bump (proj st) s
  set (upd st m)
  return s ++ "#" ++ toString i

/-- fresh.ml:20-26 `refresh_id`: strip an existing `#N` suffix back to the
base name, then fresh. -/
private def stripHash (s : String) : String :=
  let cs := s.toList
  match cs.reverse.findIdx? (· == '#') with
  | some i => String.ofList (cs.take (cs.length - 1 - i))
  | none => s

def freshVarid [Monad m] (s : String) : StateT St m String :=
  freshId (·.varids) (fun st m => { st with varids := m }) s

def freshTypid [Monad m] (s : String) : StateT St m String :=
  freshId (·.typids) (fun st m => { st with typids := m }) s

def freshDefid [Monad m] (s : String) : StateT St m String :=
  freshId (·.defids) (fun st m => { st with defids := m }) s

def freshGramid [Monad m] (s : String) : StateT St m String :=
  freshId (·.gramids) (fun st m => { st with gramids := m }) s

/-- fresh.ml:33-36 `refresh_*`. -/
def refreshVarid [Monad m] (x : Id) : StateT St m Id := freshVarid (stripHash x)
def refreshTypid [Monad m] (x : Id) : StateT St m Id := freshTypid (stripHash x)
def refreshDefid [Monad m] (x : Id) : StateT St m Id := freshDefid (stripHash x)
def refreshGramid [Monad m] (x : Id) : StateT St m Id := freshGramid (stripHash x)

end SpecTecLean.Il.Fresh
