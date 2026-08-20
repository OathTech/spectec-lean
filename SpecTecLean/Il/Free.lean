import SpecTecLean.Il.Ast
/-!
Free/bound identifier sets: mirrors `deps/spectec/spectec/src/xl/gen_free.ml`
(the `Sets` structure and aggregates) and `deps/spectec/spectec/src/il/free.ml`
(spectec @ acc6e834; the vendored patch does not touch these).

Divergences: OCaml `Set.Make(String)` is a balanced tree; `IdSet` here is a
sorted, deduplicated `List String` — same abstract set semantics,
deterministic, adequate for the small sets involved. free.ml's
`Debug_log` wrappers (free.ml:23-26,58-61,136-139) are logging-only and
not mirrored. `HintD` cases (free.ml:182-188,204,213) have no Lean
counterpart (hints absent from the dump; see Il/Ast.lean).
-/

namespace SpecTecLean.Il

/-- Sorted-dedup string set (see header). -/
abbrev IdSet := List String

namespace IdSet

def empty : IdSet := []

def singleton (x : String) : IdSet := [x]

def union (a b : IdSet) : IdSet :=
  match a, b with
  | [], b => b
  | a, [] => a
  | x :: a', y :: b' =>
    if x < y then x :: union a' (y :: b')
    else if y < x then y :: union (x :: a') b'
    else x :: union a' b'
  termination_by a.length + b.length

def inter (a b : IdSet) : IdSet :=
  match a, b with
  | [], _ | _, [] => []
  | x :: a', y :: b' =>
    if x < y then inter a' (y :: b')
    else if y < x then inter (x :: a') b'
    else x :: inter a' b'
  termination_by a.length + b.length

def diff (a b : IdSet) : IdSet :=
  match a, b with
  | [], _ => []
  | a, [] => a
  | x :: a', y :: b' =>
    if x < y then x :: diff a' (y :: b')
    else if y < x then diff (x :: a') b'
    else diff a' b'
  termination_by a.length + b.length

def subset (a b : IdSet) : Bool := (diff a b).isEmpty
def disjoint (a b : IdSet) : Bool := (inter a b).isEmpty
def mem (x : String) (a : IdSet) : Bool := a.contains x

end IdSet

/-- gen_free.ml:10-11 `sets`. -/
structure Sets where
  typid : IdSet := []
  relid : IdSet := []
  varid : IdSet := []
  defid : IdSet := []
  gramid : IdSet := []
deriving Repr, BEq, Inhabited

namespace Sets

/-- gen_free.ml:13-19. -/
def empty : Sets := {}

/-- gen_free.ml:21-27. -/
def union (s1 s2 : Sets) : Sets :=
  { typid := IdSet.union s1.typid s2.typid
    relid := IdSet.union s1.relid s2.relid
    varid := IdSet.union s1.varid s2.varid
    defid := IdSet.union s1.defid s2.defid
    gramid := IdSet.union s1.gramid s2.gramid }

/-- gen_free.ml:29-35. -/
def inter (s1 s2 : Sets) : Sets :=
  { typid := IdSet.inter s1.typid s2.typid
    relid := IdSet.inter s1.relid s2.relid
    varid := IdSet.inter s1.varid s2.varid
    defid := IdSet.inter s1.defid s2.defid
    gramid := IdSet.inter s1.gramid s2.gramid }

/-- gen_free.ml:37-43. -/
def diff (s1 s2 : Sets) : Sets :=
  { typid := IdSet.diff s1.typid s2.typid
    relid := IdSet.diff s1.relid s2.relid
    varid := IdSet.diff s1.varid s2.varid
    defid := IdSet.diff s1.defid s2.defid
    gramid := IdSet.diff s1.gramid s2.gramid }

/-- gen_free.ml:49-54. -/
def subset (s1 s2 : Sets) : Bool :=
  IdSet.subset s1.typid s2.typid && IdSet.subset s1.relid s2.relid &&
  IdSet.subset s1.varid s2.varid && IdSet.subset s1.defid s2.defid &&
  IdSet.subset s1.gramid s2.gramid

/-- gen_free.ml:56-61. -/
def disjoint (s1 s2 : Sets) : Bool :=
  IdSet.disjoint s1.typid s2.typid && IdSet.disjoint s1.relid s2.relid &&
  IdSet.disjoint s1.varid s2.varid && IdSet.disjoint s1.defid s2.defid &&
  IdSet.disjoint s1.gramid s2.gramid

end Sets

infixl:65 " ⊎ " => Sets.union      -- gen_free.ml:45 (++)
infixl:70 " ⊟ " => Sets.diff       -- gen_free.ml:47 (--)

namespace Free

/-- gen_free.ml:66-70. -/
def freeTypid (x : Id) : Sets := { typid := [x] }
def freeRelid (x : Id) : Sets := { relid := [x] }
def freeVarid (x : Id) : Sets := { varid := [x] }
def freeDefid (x : Id) : Sets := { defid := [x] }
def freeGramid (x : Id) : Sets := { gramid := [x] }

/-- gen_free.ml:72-76 (`_` binds nothing). -/
def boundTypid (x : Id) : Sets := if x == "_" then {} else freeTypid x
def boundRelid (x : Id) : Sets := if x == "_" then {} else freeRelid x
def boundVarid (x : Id) : Sets := if x == "_" then {} else freeVarid x
def boundDefid (x : Id) : Sets := if x == "_" then {} else freeDefid x
def boundGramid (x : Id) : Sets := if x == "_" then {} else freeGramid x

/-- gen_free.ml:83 `free_opt`. -/
def freeOpt (f : α → Sets) : Option α → Sets
  | none => {}
  | some x => f x

/-- gen_free.ml:84 `free_list`. -/
def freeList (f : α → Sets) (xs : List α) : Sets :=
  xs.foldl (fun s x => s ⊎ f x) {}

mutual

/-- free.ml:9-12 `free_iter`. -/
def freeIter : Iter → Sets
  | .opt | .list | .list1 => {}
  | .listN e _ => freeExp e

/-- free.ml:14-17 `bound_iter`. -/
def boundIter : Iter → Sets
  | .opt | .list | .list1 => {}
  | .listN _ xo => freeOpt boundVarid xo

/-- free.ml:22-31 `free_typ` (note: notes are NOT traversed, matching
free.ml which reads `.it` only). -/
def freeTyp : Typ → Sets
  | .varT x args =>
    freeTypid x ⊎ (args.attach.map (fun ⟨a, _⟩ => freeArg a)).foldl Sets.union {}
  | .boolT | .numT _ | .textT => {}
  | .tupT xts => freeTypbinds xts
  | .iterT t1 it => freeTyp t1 ⊎ freeIter it

/-- free.ml:33-36 `bound_typ`. -/
def boundTyp : Typ → Sets
  | .tupT xts => boundTypbinds xts
  | _ => {}

/-- free.ml:38-41. -/
def freeTypbind : TypBind → Sets
  | .mk _ t => freeTyp t

def boundTypbind : TypBind → Sets
  | .mk x _ => boundVarid x

def freeTypbinds : List TypBind → Sets
  | [] => {}
  | xt :: xts => freeTypbind xt ⊎ (freeTypbinds xts ⊟ boundTypbind xt)

def boundTypbinds (xts : List TypBind) : Sets :=
  (xts.attach.map (fun ⟨xt, _⟩ => boundTypbind xt)).foldl Sets.union {}

/-- free.ml:43-47 `free_deftyp`. -/
def freeDeftyp : DefTyp → Sets
  | .aliasT t => freeTyp t
  | .structT tfs =>
    (tfs.attach.map (fun ⟨f, _⟩ => freeTypfield f)).foldl Sets.union {}
  | .variantT tcs =>
    (tcs.attach.map (fun ⟨c, _⟩ => freeTypcase c)).foldl Sets.union {}

/-- free.ml:49-50 `free_typfield`. -/
def freeTypfield : TypField → Sets
  | .mk _ t qs prems =>
    freeTyp t ⊎ ((freeQuants qs ⊎ (freePrems prems ⊟ boundQuants qs)) ⊟ boundTyp t)

/-- free.ml:51-52 `free_typcase`. -/
def freeTypcase : TypCase → Sets
  | .mk _ t qs prems =>
    freeTyp t ⊎ ((freeQuants qs ⊎ (freePrems prems ⊟ boundQuants qs)) ⊟ boundTyp t)

/-- free.ml:57-77 `free_exp` (reads `.it` only — notes not traversed). -/
def freeExp (e : Exp) : Sets :=
  match e with
  | .mk it _note => freeExp' it

def freeExp' : Exp' → Sets
  | .varE x => freeVarid x
  | .boolE _ | .numE _ | .textE _ => {}
  | .unE _ _ e1 | .liftE e1 | .lenE e1 | .projE e1 _ | .theE e1 => freeExp e1
  | .binE _ _ e1 e2 | .cmpE _ _ e1 e2
  | .idxE e1 e2 | .compE e1 e2 | .memE e1 e2 | .catE e1 e2 =>
    freeExp e1 ⊎ freeExp e2
  | .sliceE e1 e2 e3 | .ifE e1 e2 e3 => freeExp e1 ⊎ freeExp e2 ⊎ freeExp e3
  | .optE none => {}
  | .optE (some e1) => freeExp e1
  | .tupE es | .listE es =>
    (es.attach.map (fun ⟨e1, _⟩ => freeExp e1)).foldl Sets.union {}
  | .updE e1 p e2 | .extE e1 p e2 => freeExp e1 ⊎ freePath p ⊎ freeExp e2
  | .strE efs =>
    (efs.attach.map (fun ⟨f, _⟩ => freeExpfield f)).foldl Sets.union {}
  | .dotE e1 _ | .caseE _ e1 | .uncaseE e1 _ => freeExp e1
  | .callE x args =>
    freeDefid x ⊎ (args.attach.map (fun ⟨a, _⟩ => freeArg a)).foldl Sets.union {}
  | .iterE e1 ite => (freeExp e1 ⊟ boundIterexp ite) ⊎ freeIterexp ite
  | .cvtE e1 _ _ => freeExp e1
  | .subE e1 t1 t2 => freeExp e1 ⊎ freeTyp t1 ⊎ freeTyp t2

/-- free.ml:79. -/
def freeExpfield : ExpField → Sets
  | .mk _ e => freeExp e

/-- free.ml:81-86 `free_path`. -/
def freePath (p : Path) : Sets :=
  match p with
  | .mk it _note => freePath' it

def freePath' : Path' → Sets
  | .rootP => {}
  | .idxP p1 e => freePath p1 ⊎ freeExp e
  | .sliceP p1 e1 e2 => freePath p1 ⊎ freeExp e1 ⊎ freeExp e2
  | .dotP p1 _ => freePath p1

/-- free.ml:88-89 `free_iterexp`. -/
def freeIterexp : IterExp → Sets
  | .mk it xes =>
    freeIter it ⊎ (xes.attach.map (fun ⟨d, _⟩ => freeDom d)).foldl Sets.union {}

def freeDom : Dom → Sets
  | .mk _ e => freeExp e

/-- free.ml:91-92 `bound_iterexp`. -/
def boundIterexp : IterExp → Sets
  | .mk it xes =>
    boundIter it ⊎ (xes.attach.map (fun ⟨d, _⟩ => boundDom d)).foldl Sets.union {}

def boundDom : Dom → Sets
  | .mk x _ => boundVarid x

/-- free.ml:97-104 `free_sym`. -/
def freeSym : Sym → Sets
  | .varG x args =>
    freeGramid x ⊎ (args.attach.map (fun ⟨a, _⟩ => freeArg a)).foldl Sets.union {}
  | .numG _ | .textG _ | .epsG => {}
  | .seqG gs | .altG gs =>
    (gs.attach.map (fun ⟨g, _⟩ => freeSym g)).foldl Sets.union {}
  | .rangeG g1 g2 => freeSym g1 ⊎ freeSym g2
  | .iterG g1 ite => (freeSym g1 ⊟ boundIterexp ite) ⊎ freeIterexp ite
  | .attrG e g1 => freeExp e ⊎ freeSym g1

/-- free.ml:109-116 `free_prem`. -/
def freePrem : Prem → Sets
  | .rulePr x args _ e =>
    freeRelid x
      ⊎ (args.attach.map (fun ⟨a, _⟩ => freeArg a)).foldl Sets.union {}
      ⊎ freeExp e
  | .ifPr e => freeExp e
  | .letPr qs e1 e2 => (freeExp e1 ⊟ boundQuants qs) ⊎ freeExp e2
  | .elsePr => {}
  | .iterPr prem1 ite => (freePrem prem1 ⊟ boundIterexp ite) ⊎ freeIterexp ite
  | .negPr prem1 => freePrem prem1

/-- free.ml:118-121 `bound_prem`. -/
def boundPrem : Prem → Sets
  | .letPr qs _ _ => boundQuants qs
  | _ => {}

/-- free.ml:123 `free_prems = free_list_dep free_prem bound_prem`. -/
def freePrems : List Prem → Sets
  | [] => {}
  | p :: ps => freePrem p ⊎ (freePrems ps ⊟ boundPrem p)

/-- free.ml:128-133 `free_arg`. -/
def freeArg : Arg → Sets
  | .expA e => freeExp e
  | .typA t => freeTyp t
  | .defA x => freeDefid x
  | .gramA g => freeSym g

/-- free.ml:135-144 `free_param`. -/
def freeParam : Param → Sets
  | .expP _ t => freeTyp t
  | .typP _ => {}
  | .defP _ ps t => freeParams ps ⊎ (freeTyp t ⊟ boundParams ps)
  | .gramP _ ps t => freeParams ps ⊎ (freeTyp t ⊟ boundParams ps)

/-- free.ml:146-151 `bound_param`. -/
def boundParam : Param → Sets
  | .expP x _ => boundVarid x
  | .typP x => boundTypid x
  | .defP x _ _ => boundDefid x
  | .gramP x _ _ => boundGramid x

/-- free.ml:157 `free_params` (free_list_dep). -/
def freeParams : List Param → Sets
  | [] => {}
  | p :: ps => freeParam p ⊎ (freeParams ps ⊟ boundParam p)

/-- free.ml:159 `bound_params` (free_list bound_param). -/
def boundParams (ps : List Param) : Sets :=
  (ps.attach.map (fun ⟨p, _⟩ => boundParam p)).foldl Sets.union {}

/-- free.ml:153-160: quants are params. -/
def freeQuants : List Param → Sets
  | [] => {}
  | q :: qs => freeParam q ⊎ (freeQuants qs ⊟ boundParam q)

def boundQuants (qs : List Param) : Sets :=
  (qs.attach.map (fun ⟨q, _⟩ => boundParam q)).foldl Sets.union {}

end

/-- free.ml:162-165 `free_inst`. -/
def freeInst : Inst → Sets
  | .mk _ qs args dt =>
    freeQuants qs ⊎ ((freeList freeArg args ⊎ freeDeftyp dt) ⊟ boundQuants qs)

/-- free.ml:167-170 `free_rule`. -/
def freeRule : Rule → Sets
  | .mk _ _ qs _ e prems =>
    freeQuants qs ⊎ ((freeExp e ⊎ freePrems prems) ⊟ boundQuants qs)

/-- free.ml:172-175 `free_clause`. -/
def freeClause : Clause → Sets
  | .mk _ qs args e prems =>
    freeQuants qs
      ⊎ ((freeList freeArg args ⊎ freeExp e ⊎ freePrems prems) ⊟ boundQuants qs)

/-- free.ml:177-180 `free_prod`. -/
def freeProd : Prod → Sets
  | .mk _ qs g e prems =>
    freeQuants qs
      ⊎ ((freeSym g ⊎ freeExp e ⊎ freePrems prems) ⊟ boundQuants qs)

/-- free.ml:190-203 `free_def`. -/
def freeDef : Def → Sets
  | .typD _ _ ps insts =>
    freeParams ps ⊎ (freeList freeInst insts ⊟ boundParams ps)
  | .relD _ _ ps _ t rules =>
    freeParams ps ⊎ ((freeTyp t ⊎ freeList freeRule rules) ⊟ boundParams ps)
  | .decD _ _ ps t clauses =>
    freeParams ps ⊎ ((freeTyp t ⊎ freeList freeClause clauses) ⊟ boundParams ps)
  | .gramD _ _ ps t prods =>
    freeParams ps ⊎ ((freeTyp t ⊎ freeList freeProd prods) ⊟ boundParams ps)
  | .recD _ ds => (ds.attach.map (fun ⟨d, _⟩ => freeDef d)).foldl Sets.union {}

/-- free.ml:206-213 `bound_def`. -/
def boundDef : Def → Sets
  | .typD x _ _ _ => boundTypid x
  | .relD x _ _ _ _ _ => boundRelid x
  | .decD x _ _ _ _ => boundDefid x
  | .gramD x _ _ _ _ => boundGramid x
  | .recD _ ds => (ds.attach.map (fun ⟨d, _⟩ => boundDef d)).foldl Sets.union {}

end Free

end SpecTecLean.Il
