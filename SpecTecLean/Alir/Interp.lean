import SpecTecLean.Alir.Ast
import SpecTecLean.XlOps
import SpecTecLean.Il.Eq
/-!
AL interpreter, pure-instruction fragment — mirror of the relevant
subset of `deps/spectec/spectec/src/backend-interpreter/interpreter.ml`
(860 lines; spectec @ acc6e834). Arc-3b stage 1.

FRAGMENT BOUNDARY (fail-closed): only what the pure-instruction
algorithms need is executable; every other construct is an explicit
`.error` — never a silent approximation. Out of scope in stage 1:
contexts (Enter/Exit/FRAME_/LABEL_, WasmContext.push_context),
the mutable Store, function calls (CallE/InvCallE/PerformI), numerics
beyond comparisons, EitherI backtracking, ReturnI.

Representation divergences (deliberate, documented):
- Upstream's global mutable state — the WasmContext value stack
  (ds.ml) — is threaded explicitly as `St`; `AlM` is the fueled
  state-error monad. Same discipline as Il/Eval.lean.
- Upstream's `AlContext` mode stack (interpreter.ml:739-786) drives a
  small-step scheduler for stepping/debugging; for the no-context
  fragment the direct recursion below computes the same final state
  (no Enter/Wasm-depth modes are reachable). Constructs that would
  need the mode stack are rejected at the boundary.
- Exceptions Trap/Fail (exception.ml; interpreter.ml:658-660) become
  monadic outcomes `.trap`/`.fail`; interpreter `failwith`/`fail_expr`
  becomes `.error`; fuel is the recursion bound (`.fuel` never caught).
-/

namespace SpecTecLean.Il.Alir

open SpecTecLean.Il

/-- Outcome classes: trap/fail mirror exception.ml's Trap/Fail;
`error` mirrors `failwith`/`fail_expr`; `fuel` is the Lean bound. -/
inductive AlErr where
  | trap
  | fail
  | error (msg : String)
  | fuel
deriving Repr, Inhabited

/-- Explicit state: the WasmContext VALUE stack (ds.ml; top = head,
mirroring push_value/pop_value list order). Contexts are out of the
stage-1 fragment. -/
structure St where
  stack : List Value := []
deriving Repr, Inhabited

abbrev AlM (α : Type) := St → Except AlErr (α × St)

namespace AlM
def pure' {α} (a : α) : AlM α := fun st => .ok (a, st)
instance : Monad AlM where
  pure := pure'
  bind m f := fun st => match m st with
    | .ok (a, st') => f a st'
    | .error e => .error e
instance : MonadExceptOf AlErr AlM where
  throw e := fun _ => .error e
  tryCatch m h := fun st => match m st with
    | .error e => h e st
    | r => r
def get : AlM St := fun st => .ok (st, st)
def set (st : St) : AlM Unit := fun _ => .ok ((), st)
end AlM

open AlM (get set)

def err {α} (msg : String) : AlM α := throw (.error msg)

/-- Environment (ds.ml `Env` — string map; assoc list mirror). -/
abbrev AlEnv := List (AlId × Value)

def lookupEnv (env : AlEnv) (x : AlId) : AlM Value :=
  match env.lookup x with
  | some v => pure v
  | none => err s!"free variable {x}"

/-- Atom name for CaseV tags (interpreter.ml uses
`Print.string_of_atom`; mirrored by XlPrint.atomToString). -/
def atomName (a : Atom) : String := XlPrint.atomToString a

/-- Mixop head atom (xl/mixop.ml `head` — first atom of the first
phrase). -/
def mixopHead : Mixop → Option Atom :=
  fun op => ((MixopEq.flatten op).flatMap id).head?

def mixopTag (op : Mixop) : String :=
  match mixopHead op with
  | some a => atomName a
  | none => ""

/-- interpreter.ml:582-587 `is_true`. -/
def isTrue : Value → Bool
  | .boolV true => true
  | .optV none => true
  | .optV (some v) => isTrue v
  | .listV vs => vs.attach.all (fun ⟨v, _⟩ => isTrue v)
  | _ => false

/-- Value-stack primitives (ds.ml WasmContext, mirrored on `St`). -/
def pushValue (v : Value) : AlM Unit := do
  let st ← get
  set { st with stack := v :: st.stack }

def popValue : AlM Value := do
  let st ← get
  match st.stack with
  | v :: rest => do set { st with stack := rest }; pure v
  | [] => err "pop on empty value stack"

def popAllValues : AlM (List Value) := do
  let st ← get
  set { st with stack := [] }
  -- ds.ml pop_value_stack returns the stack (top-first); interpreter.ml
  -- :647 reverses it into bottom-first list order
  pure st.stack.reverse

/-- Numeric comparison for `BinE` (interpreter.ml:246-261 delegates to
Num.cmp / Bool ops; stage-1 needs eq/ne/lt/gt/le/ge on nats/ints and
boolean and/or). Real/rat arithmetic fails closed as in Il/Eval. -/
def numCmp (op : BinOp) (n1 n2 : Num) : AlM Value := do
  let cmpZ (a b : Int) : AlM Value :=
    pure <| .boolV <| match op with
      | .eq => a == b | .ne => a != b | .lt => a < b
      | .gt => a > b | .le => a ≤ b | .ge => a ≥ b
      | _ => false
  match n1, n2 with
  | .nat a, .nat b => cmpZ a b
  | .int a, .int b => cmpZ a b
  | .nat a, .int b => cmpZ a b
  | .int a, .nat b => cmpZ a b
  | _, _ => err "numeric comparison unsupported for rat/real (fail-closed)"

mutual
/-- interpreter.ml:213-453 `eval_expr` — stage-1 rows only, cited per
row; everything else is a loud error. -/
def evalExpr (fuel : Nat) (env : AlEnv) (e : Expr) : AlM Value :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match e.it with
    | .numE nu => pure (.numV nu)                       -- :224
    | .boolE b => pure (.boolV b)                       -- :225
    | .unE .not e1 => do                                -- :236-238 (Bool)
      pure (.boolV (!(isTrue (← evalExpr n env e1))))
    | .binE op e1 e2 => do                              -- :246-261
      let v1 ← evalExpr n env e1
      let v2 ← evalExpr n env e2
      match op, v1, v2 with
      | .and, _, _ => pure (.boolV (isTrue v1 && isTrue v2))
      | .or, _, _ => pure (.boolV (isTrue v1 || isTrue v2))
      | .eq, _, _ =>
        -- Bool.cmpop `EqOp on values: OCaml polymorphic (=) (:254)
        -- mirrored by derived BEq on the Value mirror
        match v1, v2 with
        | .numV a, .numV b => numCmp .eq (a) (b)
        | _, _ => pure (.boolV (v1 == v2))
      | .ne, _, _ =>
        match v1, v2 with
        | .numV a, .numV b => numCmp .ne a b
        | _, _ => pure (.boolV (v1 != v2))
      | _, .numV a, .numV b => numCmp op a b
      | _, _, _ => err "binE row outside stage-1 fragment"
    | .varE "s" =>                                      -- :364-365
      err "implicit store variable `s` outside stage-1 fragment"
    | .varE x => lookupEnv env x                        -- :366
    | .caseE op es => do                                -- :348-352
      pure (.caseV (mixopTag op) (← es.attach.mapM
        (fun ⟨e1, _⟩ => evalExpr n env e1)))
    | .listE es => do                                   -- :298
      pure (.listV (← es.attach.mapM (fun ⟨e1, _⟩ => evalExpr n env e1)))
    | .optE none => pure (.optV none)                   -- :353
    | .optE (some e1) => do pure (.optV (some (← evalExpr n env e1)))
    | .tupE es => do                                    -- :354
      pure (.tupV (← es.attach.mapM (fun ⟨e1, _⟩ => evalExpr n env e1)))
    | .lenE e1 => do                                    -- :320-321
      match ← evalExpr n env e1 with
      | .listV vs => pure (.numV (.nat vs.length))
      | _ => err "lenE on non-list"
    | .catE e1 e2 => do                                 -- :316-319
      match ← evalExpr n env e1, ← evalExpr n env e2 with
      | .listV a, .listV b => pure (.listV (a ++ b))
      | .optV a, .listV b => pure (.listV (a.toList ++ b))
      | .listV a, .optV b => pure (.listV (a ++ b.toList))
      | _, _ => err "catE on non-sequences"
    | .liftE e1 => do                                   -- :314-315
      match ← evalExpr n env e1 with
      | .optV v? => pure (.listV v?.toList)
      | _ => err "liftE on non-option"
    | .iterE (.mk (.varE x) _) (.mk _ [(x', src)]) =>   -- :368-369
      if x == x' then evalExpr n env src
      else err "iterE row outside stage-1 fragment"
    | .isDefinedE e1 => do                              -- :403-408
      match ← evalExpr n env e1 with
      | .optV v? => pure (.boolV v?.isSome)
      | _ => err "isDefinedE on non-option"
    | .isCaseOfE e1 a => do                             -- :409-413
      match ← evalExpr n env e1 with
      | .caseV tag _ => pure (.boolV (atomName a == tag))
      | _ => pure (.boolV false)
    | .topValueE _ => do                                -- :447-449
      -- upstream ignores the type payload ("TODO: type check")
      let st ← get
      pure (.boolV (st.stack.length > 0))
    | .topValuesE e1 => do                              -- :450-452
      match ← evalExpr n env e1 with
      | .numV (.nat i) => do
        let st ← get
        pure (.boolV (st.stack.length ≥ i))
      | _ => err "topValuesE count not a nat"
    | _ => err "expr outside stage-1 fragment (fail-closed)"
end

/-- interpreter.ml:468-538 `assign` — stage-1 rows, cited; fail-closed
rest. Returns the extended environment. -/
def assign (fuel : Nat) (lhs : Expr) (rhs : Value) (env : AlEnv) :
    AlM AlEnv :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match lhs.it, rhs with
    | .varE x, _ => pure ((x, rhs) :: env)              -- :470
    | .iterE (.mk (.varE x1) _) (.mk it [(x2, lhs')]), .listV _ => -- :471-472
      match it with
      | .list | .list1 =>
        if x1 == x2 then assign n lhs' rhs env
        else err "iterE assign row outside stage-1 fragment"
      | _ => err "iterE assign row outside stage-1 fragment"
    | .iterE e1 (.mk iter xes), _ => do                 -- :473-496
      let vs ← match rhs, iter with
        | .listV vs, _ => pure vs
        | .optV v?, .opt => pure v?.toList
        | _, _ => err "iter assign on non-sequence"
      let envs ← vs.mapM (fun v => assign n e1 v [])
      let env' ← match iter with
        | .listN len none =>
          assign n len (.numV (.nat vs.length)) env     -- :480-482
        | .listN _ (some _) =>
          err "invalid assignment: iter with index (interpreter.ml:483)"
        | _ => pure env
      xes.foldlM (fun envA (x, e) => do                 -- :488-496
        let vsX ← envs.mapM (fun envI => lookupEnv envI x)
        let v := match iter with
          | .opt => .optV vsX.head?
          | _ => .listV vsX
        assign n e v envA) env'
    | .tupE ls, .tupV rs =>                             -- :497-499
      if ls.length == rs.length then
        (ls.zip rs).foldrM (fun (l, r) envA => assign n l r envA) env
      else err "tup assign arity"
    | .listE ls, .listV rs =>                           -- :500-502
      if ls.length == rs.length then
        (ls.zip rs).foldrM (fun (l, r) envA => assign n l r envA) env
      else err "list assign arity"
    | .caseE op ls, .caseV rtag rs =>                   -- :503-511
      if ls.length == rs.length && mixopTag op == rtag then
        (ls.zip rs).foldrM (fun (l, r) envA => assign n l r envA) env
      else err s!"case assign mismatch: {mixopTag op} vs {rtag}"
    | .optE (some l), .optV (some r) => assign n l r env -- :512
    | _, _ => err "assign row outside stage-1 fragment (fail-closed)"

/-- interpreter.ml:571-575 `assign_param`. -/
def assignParam (fuel : Nat) (p : Arg) (v : Value) (env : AlEnv) :
    AlM AlEnv :=
  match p with
  | .expA e => assign fuel e v env
  | .typA _ => err "TypA param (interpreter.ml:574 assert false)"
  | .defA x => pure (("$" ++ x, v) :: env)

/-- Algorithm table: rule algorithms keyed by instruction tag
(ds.ml lookup_algo via create_context; RuleA algorithms are looked up
by their mixop head, main.ml match_algo_name). -/
abbrev Algos := List (String × (List Arg × List Instr))

mutual
/-- interpreter.ml:590-719 `step_instr`, direct-recursion form (see
header divergence note) — stage-1 rows, cited. -/
def runInstrs (algos : Algos) (fuel : Nat) (env : AlEnv)
    (il : List Instr) : AlM AlEnv :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match il with
    | [] => pure env
    | i :: rest => do
      match i with
      | .ifI cond thn els => do                         -- :592-596
        let v ← evalExpr n env cond
        let env' ← runInstrs algos n env (if isTrue v then thn else els)
        runInstrs algos n env' rest
      | .assertI cond => do                             -- :605-609
        if isTrue (← evalExpr n env cond) then
          runInstrs algos n env rest
        else err "assertion fail"
      | .pushI e => do                                  -- :610-621
        match ← evalExpr n env e with
        | .caseV "FRAME_" _ =>
          err "FRAME_ push outside stage-1 fragment"
        | .listV vs => do
          vs.forM pushValue
          runInstrs algos n env rest
        | v => do
          pushValue v
          runInstrs algos n env rest
      | .popI e => do                                   -- :622-645
        match e.it with
        | .caseE op _ =>
          if mixopTag op == "FRAME_" then
            err "FRAME_ pop outside stage-1 fragment"
          else do
            let env' ← assign n e (← popValue) env      -- :642-644
            runInstrs algos n env' rest
        | .iterE (.mk (.varE x) _) (.mk (.listN eN none) [(x', e')]) => do
          if x == x' then do                            -- :633-641
            match ← evalExpr n env eN with
            | .numV (.nat i) => do
              let vs ← (List.range i).mapM (fun _ => popValue)
              let env' ← assign n e' (.listV vs.reverse) env
              runInstrs algos n env' rest
            | _ => err "pop count not a nat"
          else err "popI iter row outside stage-1 fragment"
        | _ => do
          let env' ← assign n e (← popValue) env        -- :642-644
          runInstrs algos n env' rest
      | .popAllI e => do                                -- :646-649
        let vs ← popAllValues
        let env' ← assign n e (.listV vs) env
        runInstrs algos n env' rest
      | .letI lhs rhs => do                             -- :650-652
        let v ← evalExpr n env rhs
        let env' ← assign n lhs v env
        runInstrs algos n env' rest
      | .trapI => throw .trap                           -- :658
      | .failI => throw .fail                           -- :660
      | .nopI => runInstrs algos n env rest             -- :661
      | .executeI e => do                               -- :665-667
        let v ← evalExpr n env e
        execWasm algos n v
        runInstrs algos n env rest
      | .executeSeqI e => do                            -- :668-675
        match ← evalExpr n env e with
        | .listV vs => do
          vs.forM (execWasm algos n)
          runInstrs algos n env rest
        | _ => err "executeSeqI on non-sequence"
      | _ => err "instr outside stage-1 fragment (fail-closed)"

/-- interpreter.ml:724-733 `step_wasm` + :788-809 `create_context`,
direct form. CONST/VCONST push; other cases dispatch their algorithm.
Host functions and the version≤2 REF.NULL rows are out of fragment. -/
def execWasm (algos : Algos) (fuel : Nat) (v : Value) : AlM Unit :=
  match fuel with
  | 0 => throw .fuel
  | n+1 =>
    match v with
    | .caseV "CONST" _ | .caseV "VCONST" _ => pushValue v -- :729-730
    | .caseV tag args => do                             -- :732 + :788-809
      match algos.lookup tag with
      | none => err s!"no algorithm for instruction `{tag}`"
      | some (params, body) => do
        if params.length != args.length then
          err s!"algorithm `{tag}` arity: {params.length} params, {args.length} args"
        else do
          let env ← (params.zip args).foldrM             -- :804-807
            (fun (p, a) envA => assignParam n p a envA) []
          let _ ← runInstrs algos n env body
          pure ()
    | _ => err "cannot step a wasm instr (interpreter.ml:733)"
end

/-- Entry: execute a sequence of instruction VALUES left to right on an
initially empty stack (the wasm-side instruction order; values push,
instructions dispatch). Returns the final stack BOTTOM-FIRST. -/
def runSeq (algos : Algos) (fuel : Nat) (instrs : List Value) :
    Except AlErr (List Value) :=
  match (instrs.forM (execWasm algos fuel)) {} with
  | .ok (_, st) => .ok st.stack.reverse
  | .error e => .error e

end SpecTecLean.Il.Alir
