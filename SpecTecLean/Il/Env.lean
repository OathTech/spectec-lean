import SpecTecLean.Il.Ast
/-!
Definition environments, mirroring `deps/spectec/spectec/src/il/env.ml`.

Divergences: OCaml `Map.Make(String)` becomes an association list wrapper
(`SMap`) — small key counts, deterministic, adequate. `find` errors carry
the message text of env.ml:49 but as `Except` values (no positions on ids
in our AST; the def-level region is the caller's to add). env.ml's
mutable `phase` ref (env.ml:7) is a message prefix only — callers pass
the phase string. `HintD` case (env.ml:106) has no Lean counterpart.
-/

namespace SpecTecLean.Il

/-- Minimal string map (assoc list, last bind wins via cons). -/
structure SMap (α : Type) where
  entries : List (String × α) := []
deriving Repr, Inhabited

namespace SMap

def empty : SMap α := {}

def find? (m : SMap α) (x : String) : Option α := m.entries.lookup x

def mem (m : SMap α) (x : String) : Bool := (m.find? x).isSome

/-- OCaml `Map.add` replaces; cons + lookup-first gives the same
observable behavior. -/
def add (m : SMap α) (x : String) (v : α) : SMap α :=
  { entries := (x, v) :: m.entries }

end SMap

/-- env.ml:17-21 the five definition payloads. -/
abbrev VarDef := Typ
abbrev TypDef := List Param × List Inst
abbrev RelDef := List Param × Mixop × Typ × List Rule
abbrev DefDef := List Param × Typ × List Clause
abbrev GramDef := List Param × Typ × List Prod

/-- env.ml:23-29 `t`. -/
structure Env where
  vars : SMap VarDef := {}
  typs : SMap TypDef := {}
  defs : SMap DefDef := {}
  rels : SMap RelDef := {}
  grams : SMap GramDef := {}
deriving Inhabited

namespace Env

def empty : Env := {}

/-- env.ml:52-60 `bind` (`"_"` binds nothing; the duplicate check is
disabled upstream too, env.ml:55-58). -/
private def bind (m : SMap α) (x : Id) (v : α) : SMap α :=
  if x == "_" then m else m.add x v

def bindVar (env : Env) (x : Id) (v : VarDef) : Env :=
  { env with vars := bind env.vars x v }
def bindTyp (env : Env) (x : Id) (v : TypDef) : Env :=
  { env with typs := bind env.typs x v }
def bindDef (env : Env) (x : Id) (v : DefDef) : Env :=
  { env with defs := bind env.defs x v }
def bindRel (env : Env) (x : Id) (v : RelDef) : Env :=
  { env with rels := bind env.rels x v }
def bindGram (env : Env) (x : Id) (v : GramDef) : Env :=
  { env with grams := bind env.grams x v }

/-- env.ml:47-50 `find` (as Except; message text mirrored). -/
private def find (space : String) (m : SMap α) (x : Id) : Except String α :=
  match m.find? x with
  | none => .error s!"undeclared {space} `{x}`"
  | some v => .ok v

def findVar (env : Env) (x : Id) := find "variable" env.vars x
def findTyp (env : Env) (x : Id) := find "type" env.typs x
def findDef (env : Env) (x : Id) := find "definition" env.defs x
def findRel (env : Env) (x : Id) := find "relation" env.rels x
def findGram (env : Env) (x : Id) := find "grammar" env.grams x

def findVar? (env : Env) (x : Id) := env.vars.find? x
def findTyp? (env : Env) (x : Id) := env.typs.find? x
def findDef? (env : Env) (x : Id) := env.defs.find? x
def findRel? (env : Env) (x : Id) := env.rels.find? x
def findGram? (env : Env) (x : Id) := env.grams.find? x

/-- env.ml:99-106 `env_of_def`. -/
def ofDef (env : Env) : Def → Env
  | .typD x _ ps insts => env.bindTyp x (ps, insts)
  | .decD x _ ps t clauses => env.bindDef x (ps, t, clauses)
  | .relD x _ ps op t rules => env.bindRel x (ps, op, t, rules)
  | .gramD x _ ps t prods => env.bindGram x (ps, t, prods)
  | .recD _ ds => ds.attach.foldl (fun e ⟨d, _⟩ => ofDef e d) env

/-- env.ml:108-109 `env_of_script`. -/
def ofScript (ds : Script) : Env :=
  ds.foldl ofDef empty

end Env

end SpecTecLean.Il
