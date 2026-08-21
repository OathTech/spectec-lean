import SpecTecLean.Sexpr
import SpecTecLean.OcamlEscape
import SpecTecLean.Il.Eval
/-!
Generic AL values (the meta-interpreter's value grammar, al/ast.ml:31-40)
and a TYPE-DIRECTED decoder into spec-typed IL expressions (arc-2
stage 7). The OCaml harness driver (`--wast-sexpr`, vendored patch)
serializes `Construct.al_of_module`/`al_of_value` output generically:

  NumV (`Nat n) → (N n)      NumV (`Int i) → (I ±i)
  BoolV → (B b)              TextV → (T "…")
  ListV → (L v*)             StrV → (S (F "key" v)*)
  CaseV id args → (C "id" v*)  OptV → (O v?)   TupV → (U v*)

Decoding rules (fail-closed):
- AL `CaseV` ids are the case mixop's HEAD atom rendering
  (construct.ml names; `Mixop.head`, mixop.ml:59-65) — candidate cases
  with that head are tried in variant order, first successful payload
  decode wins.
- `TextV` decodes at `textT`, and at char-iteration types (`name = char*`,
  1.1-syntax.values.spectec:93; construct.ml:1101 encodes names as TextV)
  as the codepoint list.
- Every decoded expression's note is the DECLARED type at that position.
-/

namespace SpecTecLean.Il

inductive AlValue where
  | num (n : Num)
  | bool (b : Bool)
  | text (s : String)
  | list (vs : List AlValue)
  | str (fields : List (String × AlValue))
  | case (id : String) (args : List AlValue)
  | opt (v? : Option AlValue)
  | tup (vs : List AlValue)
deriving Repr, Inhabited

namespace AlValue

open SpecTecLean (Sexpr)

/-- Fail-closed reader of the driver's serialization (see header). -/
def ofSexpr : Sexpr → Except String AlValue
  | .node "N" [.atom d] =>
    match d.toNat? with
    | some n => .ok (.num (.nat n))
    | none => .error s!"bad N payload {d}"
  | .node "I" [.atom d] =>
    let sign := (d.take 1).toString
    match sign, (d.drop 1).toString.toNat? with
    | "+", some n => .ok (.num (.int n))
    | "-", some n => .ok (.num (.int (-(Int.ofNat n))))
    | _, _ => .error s!"bad I payload {d}"
  | .node "B" [.atom "true"] => .ok (.bool true)
  | .node "B" [.atom "false"] => .ok (.bool false)
  | .node "T" [t] => do
    match OcamlEscape.unquote (tok t) with
    | .ok s => .ok (.text s)
    | .error e => .error e
  | .node "L" vs => do .ok (.list (← vs.attach.mapM (fun ⟨v, _⟩ => ofSexpr v)))
  | .node "S" fs => do
    .ok (.str (← fs.attach.mapM (fun ⟨f, _⟩ =>
      match f with
      | .node "F" [k, v] => do
        match OcamlEscape.unquote (tok k) with
        | .ok ks => do .ok (ks, ← ofSexpr v)
        | .error e => .error e
      | _ => .error "bad S field")))
  | .node "C" (id :: args) => do
    match OcamlEscape.unquote (tok id) with
    | .ok ids => do
      .ok (.case ids (← args.attach.mapM (fun ⟨v, _⟩ => ofSexpr v)))
    | .error e => .error e
  | .node "O" [] => .ok (.opt none)
  | .node "O" [v] => do .ok (.opt (some (← ofSexpr v)))
  | .node "U" vs => do .ok (.tup (← vs.attach.mapM (fun ⟨v, _⟩ => ofSexpr v)))
  | x => .error s!"unknown AL value form {((Sexpr.pp 0 100000 x).2.take 80).toString}"
  termination_by x => sizeOf x
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
      | (rename_i hm _; have := List.sizeOf_lt_of_mem hm; simp_all; omega)
where
  tok : Sexpr → String
    | .atom s => s
    | _ => ""

end AlValue

namespace AlDecode

open Eval

/-- mixop.ml:59-65 `head`. -/
def mixopHead : Mixop → Option Atom
  | .arg => none
  | .atom a => some a
  | .brack a _ _ => some a
  | .infix m a _ => match mixopHead m with | none => some a | s => s
  | .seq [] => none
  | .seq (m :: ms) =>
    match mixopHead m with
    | none => mixopHead (.seq ms)
    | s => s

/-- The AL CaseV naming: head atom's `to_string`. -/
def caseName (m : Mixop) : Option String :=
  (mixopHead m).map XlPrint.atomToString

/-- All atom renderings of a mixop (construct.ml sometimes names a case
by a NON-head atom, e.g. the FUNC comptype is `"->"`, construct.ml:1140).
A case is a decode candidate if the AL id matches ANY of its atoms;
payload decoding disambiguates. -/
def caseAtoms : Mixop → List String
  | .arg => []
  | .atom a => [XlPrint.atomToString a]
  | .brack l m r =>
    XlPrint.atomToString l :: caseAtoms m ++ [XlPrint.atomToString r]
  | .infix m1 a m2 =>
    caseAtoms m1 ++ [XlPrint.atomToString a] ++ caseAtoms m2
  | .seq ms => ms.attach.flatMap (fun ⟨m1, _⟩ => caseAtoms m1)

/-- Type head description for decode diagnostics. -/
def typDesc : Typ → String
  | .varT x args => s!"(var {x}/{args.length})"
  | .boolT => "bool" | .numT nt => s!"(num {reprStr nt})" | .textT => "text"
  | .tupT xts => s!"(tup/{xts.length})"
  | .iterT t it =>
    s!"(iter {typDesc t} {match it with | .opt => "?" | _ => "*"})"

mutual

/-- Wrap a bare value into a SINGLETON-case variant (notation families
like `list(X) = X*` elaborate to a one-case variant with an anonymous
`%` mixop — 1.1-syntax.values.spectec:84 — whose payload carries the
actual content). -/
def decodeWrapSingleton (env : Env) (fuel : Nat) (v : AlValue) (t : Typ) :
    EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match ← reduceTypdef env n t with
    | .variantT [.mk op ct _ _] => do
      let payload ← decodePayload env n [v] ct
      pure (.mk (.caseE op payload) t)
    | _ => err s!"decode: value/type mismatch at {typDesc t}"

/-- Decode an AL value at a declared type (see header). -/
def decode (env : Env) (fuel : Nat) (v : AlValue) (t : Typ) : EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match v with
    | .text s => do
      match ← reduceTyp env n t with
      | .textT => pure (.mk (.textE s) t)
      | .iterT t1 .list => do
        -- names are char* (chars are constrained nat wrappers); decode
        -- each codepoint at the element type
        let chars ← s.toList.mapM (fun c =>
          decode env n (.num (.nat c.toNat)) t1)
        pure (.mk (.listE chars) t)
      | _ => decodeWrapSingleton env n v t
    | .num nv => do
      match ← reduceTyp env n t with
      | .numT .nat =>
        match nv with
        | .nat _ => pure (.mk (.numE nv) t)
        | .int i => if 0 ≤ i then pure (.mk (.numE (.nat i.toNat)) t)
                    else err "decode: negative at nat type"
        | _ => err "decode: non-integer NumV"
      | .numT .int =>
        match nv with
        | .nat m => pure (.mk (.numE (.int m)) t)
        | .int _ => pure (.mk (.numE nv) t)
        | _ => err "decode: non-integer NumV"
      | _ => decodeWrapSingleton env n v t
    | .bool b => do
      match ← reduceTyp env n t with
      | .boolT => pure (.mk (.boolE b) t)
      | _ => decodeWrapSingleton env n v t
    | .list vs => do
      match ← reduceTyp env n t with
      | .iterT _ .opt => err "decode: ListV at option type"
      | .iterT t1 _ => do
        pure (.mk (.listE (← vs.mapM (fun v1 => decode env n v1 t1))) t)
      | _ => decodeWrapSingleton env n v t
    | .opt v? => do
      match ← reduceTyp env n t with
      | .iterT t1 .opt => do
        match v? with
        | none => pure (.mk (.optE none) t)
        | some v1 => pure (.mk (.optE (some (← decode env n v1 t1))) t)
      | _ => decodeWrapSingleton env n v t
    | .tup vs => do
      match ← reduceTyp env n t with
      | .tupT binds => do
        let (es, _) ← decodeTup env n vs binds Subst.empty
        pure (.mk (.tupE es) t)
      | _ => decodeWrapSingleton env n v t
    | .str fields => do
      match ← reduceTypdef env n t with
      | .structT tfs => do
        let efs ← tfs.mapM (fun tf =>
          match tf with
          | .mk atom tft _ _ => do
            let key := XlPrint.atomToString atom
            match fields.lookup key with
            | some v1 => do
              pure (ExpField.mk atom (← decode env n v1 tft))
            | none => err s!"decode: missing record field {key}")
        if fields.length != tfs.length then
          err "decode: extra record fields"
        else
          pure (.mk (.strE efs) t)
      | _ => err "decode: StrV at non-record type"
    | .case id args => do
      match ← reduceTypdef env n t with
      | .variantT tcs => do
        -- construct.ml names atom-less notation cases "" (e.g.
        -- globaltype = mut? valtype, construct.ml:1202)
        let cands := tcs.filter (fun c =>
          match c with
          | .mk op _ _ _ =>
            if id == "" then (caseAtoms op).isEmpty
            else (caseAtoms op).contains id)
        if cands.isEmpty then
          err s!"decode: no case named {id} in variant {typDesc t}"
        else do
          let r ← cands.foldlM
            (fun (acc : Option Exp) c => do
              match acc with
              | some _ => pure acc
              | none =>
                match c with
                | .mk op ct _ _ =>
                  catchIrredFailure
                    (do
                      let payload ← decodePayload env n args ct
                      pure (some (Exp.mk (.caseE op payload) t)))
                    (fun _ => pure none))
            (none : Option Exp)
          match r with
          | some e => pure e
          | none => err s!"decode: no payload-compatible case {id} in {typDesc t}"
      | _ => err s!"decode: CaseV {id} at non-variant type {typDesc t}"

/-- Decode a case payload: tuple payloads consume the args positionally
(dependently, threading component substitution); non-tuple payloads take
exactly one arg. -/
def decodePayload (env : Env) (fuel : Nat) (args : List AlValue)
    (ct : Typ) : EvalM Exp :=
  match fuel with
  | 0 => throw .fuel
  | n+1 => do
    match ct with
    | .tupT binds => do
      let (es, _) ← decodeTup env n args binds Subst.empty
      pure (.mk (.tupE es) ct)
    | _ =>
      match args with
      | [v1] => decode env n v1 ct
      | _ => throw (.failure "decode: payload arity mismatch")

/-- Positional dependent-tuple decoding (types may reference earlier
binders; substitute as we go). -/
def decodeTup (env : Env) (fuel : Nat) (vs : List AlValue)
    (binds : List TypBind) (s : Subst) : EvalM (List Exp × Subst) :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match vs, binds with
    | [], [] => pure ([], s)
    | v1 :: vs', .mk x tI :: binds' => do
      let tI' ← liftS (Subst.substTypOpt s tI)
      let e1 ← decode env n v1 tI'
      let (es, s') ← decodeTup env n vs' binds' (Subst.addVarid s x e1)
      pure (e1 :: es, s')
    | _, _ => throw (.failure "decode: tuple arity mismatch")

end

end AlDecode

end SpecTecLean.Il
