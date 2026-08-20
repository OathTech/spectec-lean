import SpecTecLean.Sexpr
import SpecTecLean.OcamlEscape
import SpecTecLean.Il.Ast

/-!
IL → S-expression, a function-for-function mirror of
`deps/spectec/spectec/src/backend-ast/print.ml` (spectec @ acc6e834).
Together with `Sexpr.renderScript` this reproduces `--ast -o` output
byte-for-byte (gate requirement).

Divergence note: `script` (print.ml:226-227) filters out the `Atom ""`
that `HintD` prints as; our `Def` has no hint constructor (see Il/Ast.lean
header), so there is nothing to filter.
-/
namespace SpecTecLean.Il

open SpecTecLean (Sexpr)

/-! ## Literals (print.ml:9-20) -/

/-- print.ml:11 (`Bool.to_string`). -/
def boolToSexpr (b : Bool) : Sexpr := .atom (if b then "true" else "false")

/-- print.ml:12 `text`. -/
def textToSexpr (t : String) : Sexpr := .atom (OcamlEscape.quote t)

/-- print.ml:13 `id`. -/
def idToSexpr (x : Id) : Sexpr := textToSexpr x

/-- print.ml:14 `mixop` (token, see Il/Ast.lean header). -/
def mixopToSexpr (op : Mixop) : Sexpr := textToSexpr op

/-- print.ml:16-20 `num`. `int` always carries a sign (print.ml:18);
`rat` is `num/den` (print.ml:19); `real` re-emits the raw token. -/
def numToSexpr : Num → Sexpr
  | .nat n => .node "nat" [.atom (toString n)]
  | .int i =>
    .node "int" [.atom ((if 0 ≤ i then "+" else "-") ++ toString i.natAbs)]
  | .rat p q => .node "rat" [.atom s!"{p}/{q}"]
  | .real raw => .node "real" [.atom raw]

/-! ## Operators (print.ml:23-50, xl name tables) -/

/-- print.ml:25-30 (reachable cases only, see Il/Ast.lean). -/
def unopToSexpr : UnOp → Sexpr
  | .not => .atom "not"
  | .plus => .atom "plus"
  | .minus => .atom "minus"

/-- print.ml:32-42. -/
def binopToSexpr : BinOp → Sexpr
  | .and => .atom "and"
  | .or => .atom "or"
  | .impl => .atom "impl"
  | .equiv => .atom "equiv"
  | .add => .atom "add"
  | .sub => .atom "sub"
  | .mul => .atom "mul"
  | .div => .atom "div"
  | .mod => .atom "mod"
  | .pow => .atom "pow"

/-- print.ml:44-50. -/
def cmpopToSexpr : CmpOp → Sexpr
  | .eq => .atom "eq"
  | .ne => .atom "ne"
  | .lt => .atom "lt"
  | .gt => .atom "gt"
  | .le => .atom "le"
  | .ge => .atom "ge"

/-- xl/num.ml:27-31 `string_of_typ`. -/
def numtypName : NumTyp → String
  | .nat => "nat"
  | .int => "int"
  | .rat => "rat"
  | .real => "real"

/-- print.ml:64-65 `numtyp` (as atom). -/
def numtypToSexpr (nt : NumTyp) : Sexpr := .atom (numtypName nt)

/-- print.ml:67-69 `optyp` (xl/bool.ml:9 gives "bool"). -/
def optypToSexpr : OpTyp → Sexpr
  | .bool => .atom "bool"
  | .num nt => numtypToSexpr nt

/-- print.ml:150 `Printf.sprintf "0x%02X"`: uppercase hex, ≥2 digits. -/
def hexByte (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  let s := String.ofList (digits.map Char.toUpper)
  "0x" ++ (if s.length < 2 then "0" ++ s else s)

/-! ## The mutual core (print.ml:55-186) -/

mutual

/-- print.ml:55-59 `iter`. -/
def iterToSexpr : Iter → Sexpr
  | .opt => .atom "opt"
  | .list => .atom "list"
  | .list1 => .atom "list1"
  | .listN e xo =>
    .node "listn" ([expToSexpr e] ++ (xo.map idToSexpr).toList)

/-- print.ml:71-78 `typ`. -/
def typToSexpr : Typ → Sexpr
  | .varT x args =>
    .node "var" ([idToSexpr x] ++ args.attach.map (fun ⟨a, _⟩ => argToSexpr a))
  | .boolT => .atom "bool"
  | .numT nt => numtypToSexpr nt
  | .textT => .atom "text"
  | .tupT binds =>
    .node "tup" (binds.attach.map (fun ⟨b, _⟩ => typbindToSexpr b))
  | .iterT t it => .node "iter" [typToSexpr t, iterToSexpr it]

/-- print.ml:86-87 `typbind`. -/
def typbindToSexpr : TypBind → Sexpr
  | .mk x t => .node "bind" [idToSexpr x, typToSexpr t]

/-- print.ml:80-84 `deftyp`. -/
def deftypToSexpr : DefTyp → Sexpr
  | .aliasT t => .node "alias" [typToSexpr t]
  | .structT tfs =>
    .node "struct" (tfs.attach.map (fun ⟨f, _⟩ => typfieldToSexpr f))
  | .variantT tcs =>
    .node "variant" (tcs.attach.map (fun ⟨c, _⟩ => typcaseToSexpr c))

/-- print.ml:89-90 `typfield` (atom printed via `mixop (Mixop.Atom at)`,
identical to a mixop token here). -/
def typfieldToSexpr : TypField → Sexpr
  | .mk at_ t qs prs =>
    .node "field" ([mixopToSexpr at_, typToSexpr t]
      ++ qs.attach.map (fun ⟨q, _⟩ => paramToSexpr q)
      ++ prs.attach.map (fun ⟨p, _⟩ => premToSexpr p))

/-- print.ml:92-93 `typcase`. -/
def typcaseToSexpr : TypCase → Sexpr
  | .mk op t qs prs =>
    .node "case" ([mixopToSexpr op, typToSexpr t]
      ++ qs.attach.map (fun ⟨q, _⟩ => paramToSexpr q)
      ++ prs.attach.map (fun ⟨p, _⟩ => premToSexpr p))

/-- print.ml:98-129 `exp`. Case order follows print.ml. -/
def expToSexpr : Exp → Sexpr
  | .varE x => .node "var" [idToSexpr x]
  | .boolE b => .node "bool" [boolToSexpr b]
  | .numE n => .node "num" [numToSexpr n]
  | .textE t => .node "text" [textToSexpr t]
  | .unE op t e2 => .node "un" [unopToSexpr op, optypToSexpr t, expToSexpr e2]
  | .binE op t e1 e2 =>
    .node "bin" [binopToSexpr op, optypToSexpr t, expToSexpr e1, expToSexpr e2]
  | .cmpE op t e1 e2 =>
    .node "cmp" [cmpopToSexpr op, optypToSexpr t, expToSexpr e1, expToSexpr e2]
  | .idxE e1 e2 => .node "idx" [expToSexpr e1, expToSexpr e2]
  | .sliceE e1 e2 e3 =>
    .node "slice" [expToSexpr e1, expToSexpr e2, expToSexpr e3]
  | .updE e1 p e2 => .node "upd" [expToSexpr e1, pathToSexpr p, expToSexpr e2]
  | .extE e1 p e2 => .node "ext" [expToSexpr e1, pathToSexpr p, expToSexpr e2]
  | .strE efs =>
    .node "struct" (efs.attach.map (fun ⟨f, _⟩ => expfieldToSexpr f))
  | .dotE e1 at_ => .node "dot" [expToSexpr e1, mixopToSexpr at_]
  | .compE e1 e2 => .node "comp" [expToSexpr e1, expToSexpr e2]
  | .memE e1 e2 => .node "mem" [expToSexpr e1, expToSexpr e2]
  | .lenE e1 => .node "len" [expToSexpr e1]
  | .tupE es => .node "tup" (es.attach.map (fun ⟨e, _⟩ => expToSexpr e))
  | .callE x args =>
    .node "call" (idToSexpr x :: args.attach.map (fun ⟨a, _⟩ => argToSexpr a))
  | .iterE e1 ie => .node "iter" ([expToSexpr e1] ++ iterexpToSexprs ie)
  | .projE e1 i => .node "proj" [expToSexpr e1, .atom (toString i)]
  | .caseE op e1 => .node "case" [mixopToSexpr op, expToSexpr e1]
  | .uncaseE e1 op => .node "uncase" [expToSexpr e1, mixopToSexpr op]
  -- print.ml:122 `List.map exp (Option.to_list eo)`, Option.map expanded
  -- for the termination checker
  | .optE none => .node "opt" []
  | .optE (some e1) => .node "opt" [expToSexpr e1]
  | .theE e1 => .node "unopt" [expToSexpr e1]
  | .listE es => .node "list" (es.attach.map (fun ⟨e, _⟩ => expToSexpr e))
  | .liftE e1 => .node "lift" [expToSexpr e1]
  | .catE e1 e2 => .node "cat" [expToSexpr e1, expToSexpr e2]
  | .cvtE e1 nt1 nt2 =>
    .node "cvt" [numtypToSexpr nt1, numtypToSexpr nt2, expToSexpr e1]
  | .subE e1 t1 t2 =>
    .node "sub" [typToSexpr t1, typToSexpr t2, expToSexpr e1]
  | .ifE e1 e2 e3 => .node "if" [expToSexpr e1, expToSexpr e2, expToSexpr e3]

/-- print.ml:131-132 `expfield`. -/
def expfieldToSexpr : ExpField → Sexpr
  | .mk at_ e => .node "field" [mixopToSexpr at_, expToSexpr e]

/-- print.ml:134-139 `path`. -/
def pathToSexpr : Path → Sexpr
  | .rootP => .atom "root"
  | .idxP p e => .node "idx" [pathToSexpr p, expToSexpr e]
  | .sliceP p e1 e2 =>
    .node "slice" [pathToSexpr p, expToSexpr e1, expToSexpr e2]
  | .dotP p at_ => .node "dot" [pathToSexpr p, mixopToSexpr at_]

/-- print.ml:141-142 `iterexp` (a LIST of sexprs, spliced by callers). -/
def iterexpToSexprs : IterExp → List Sexpr
  | .mk it doms =>
    iterToSexpr it :: doms.attach.map (fun ⟨d, _⟩ => domToSexpr d)

/-- print.ml:142 the `(dom id exp)` element. -/
def domToSexpr : Dom → Sexpr
  | .mk x e => .node "dom" [idToSexpr x, expToSexpr e]

/-- print.ml:147-157 `sym`. `NumG` prints `0x%02X` (print.ml:150). -/
def symToSexpr : Sym → Sexpr
  | .varG x args =>
    .node "var" (idToSexpr x :: args.attach.map (fun ⟨a, _⟩ => argToSexpr a))
  | .numG n => .node "num" [.atom (hexByte n)]
  | .textG t => .node "text" [textToSexpr t]
  | .epsG => .atom "eps"
  | .seqG gs => .node "seq" (gs.attach.map (fun ⟨g, _⟩ => symToSexpr g))
  | .altG gs => .node "alt" (gs.attach.map (fun ⟨g, _⟩ => symToSexpr g))
  | .rangeG g1 g2 => .node "range" [symToSexpr g1, symToSexpr g2]
  | .iterG g1 ie => .node "iter" ([symToSexpr g1] ++ iterexpToSexprs ie)
  | .attrG e g1 => .node "attr" [expToSexpr e, symToSexpr g1]

/-- print.ml:162-169 `prem`. -/
def premToSexpr : Prem → Sexpr
  | .rulePr x args op e =>
    .node "rule" (idToSexpr x
      :: args.attach.map (fun ⟨a, _⟩ => argToSexpr a)
      ++ [mixopToSexpr op, expToSexpr e])
  | .ifPr e => .node "if" [expToSexpr e]
  | .letPr e1 e2 => .node "let" [expToSexpr e1, expToSexpr e2]
  | .elsePr => .atom "else"
  | .iterPr pr ie => .node "iter" ([premToSexpr pr] ++ iterexpToSexprs ie)
  | .negPr pr => .node "neg" [premToSexpr pr]

/-- print.ml:174-179 `arg`. -/
def argToSexpr : Arg → Sexpr
  | .expA e => .node "exp" [expToSexpr e]
  | .typA t => .node "typ" [typToSexpr t]
  | .defA x => .node "def" [idToSexpr x]
  | .gramA g => .node "gram" [symToSexpr g]

/-- print.ml:181-186 `param`. -/
def paramToSexpr : Param → Sexpr
  | .expP x t => .node "exp" [idToSexpr x, typToSexpr t]
  | .typP x => .node "typ" [idToSexpr x]
  | .defP x ps t =>
    .node "def" ([idToSexpr x]
      ++ ps.attach.map (fun ⟨p, _⟩ => paramToSexpr p) ++ [typToSexpr t])
  | .gramP x ps t =>
    .node "gram" ([idToSexpr x]
      ++ ps.attach.map (fun ⟨p, _⟩ => paramToSexpr p) ++ [typToSexpr t])

end

/-! ## Definitions (print.ml:188-227) -/

/-- print.ml:188-191 `inst`. -/
def instToSexpr : Inst → Sexpr
  | .mk qs args dt =>
    .node "inst" (qs.map paramToSexpr ++ args.map argToSexpr
      ++ [deftypToSexpr dt])

/-- print.ml:193-196 `rule`. -/
def ruleToSexpr : Rule → Sexpr
  | .mk x qs op e prs =>
    .node "rule" ([idToSexpr x] ++ qs.map paramToSexpr
      ++ [mixopToSexpr op, expToSexpr e] ++ prs.map premToSexpr)

/-- print.ml:198-201 `clause`. -/
def clauseToSexpr : Clause → Sexpr
  | .mk qs args e prs =>
    .node "clause" (qs.map paramToSexpr ++ args.map argToSexpr
      ++ [expToSexpr e] ++ prs.map premToSexpr)

/-- print.ml:203-206 `prod`. -/
def prodToSexpr : Prod → Sexpr
  | .mk qs g e prs =>
    .node "prod" (qs.map paramToSexpr ++ [symToSexpr g, expToSexpr e]
      ++ prs.map premToSexpr)

/-- print.ml:208-221 `def`. -/
def defToSexpr : Def → Sexpr
  | .typD x ps insts =>
    .node "typ" ([idToSexpr x] ++ ps.map paramToSexpr
      ++ insts.map instToSexpr)
  | .relD x ps op t rules =>
    .node "rel" ([idToSexpr x] ++ ps.map paramToSexpr
      ++ [mixopToSexpr op, typToSexpr t] ++ rules.map ruleToSexpr)
  | .decD x ps t clauses =>
    .node "def" ([idToSexpr x] ++ ps.map paramToSexpr
      ++ [typToSexpr t] ++ clauses.map clauseToSexpr)
  | .gramD x ps t prods =>
    .node "gram" ([idToSexpr x] ++ ps.map paramToSexpr
      ++ [typToSexpr t] ++ prods.map prodToSexpr)
  | .recD ds => .node "rec" (ds.attach.map (fun ⟨d, _⟩ => defToSexpr d))

/-- print.ml:226-227 `script` (no HintD to filter, see header). -/
def scriptToSexprs (s : Script) : List Sexpr :=
  s.map defToSexpr

end SpecTecLean.Il
