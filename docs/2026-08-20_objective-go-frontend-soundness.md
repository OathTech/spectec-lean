# Objective: a generic SpecTec-in-Lean toolkit, first applied to proving the GoLean frontend sound

Ratified in conversation with Mike, 2026-08-20. Decision attribution below
follows the [USER]/[AGENT] discipline (docs/2026-08-20_arc1-log.md).

## The objective ([USER], 2026-08-20)

1. golean already has a GoCore semantics, but its mapping to the Go
   standard is not clean — the "GoCore models Go" trust story is
   differential testing + doctrine, not a legible correspondence.
2. SpecTec is designed for representing human-readable standards.
3. Therefore: define a human-readable Go semantics in SpecTec.
4. Then prove that the SpecTec semantics over Go surface syntax
   corresponds to the golean semantics over GoCore — i.e. **prove the
   GoLean frontend sound**.
5. Prerequisite: a way to interpret SpecTec in Lean, including
   differentially testing that interpretation. (= this repo.)

Standing directive ([USER]): prefer the strongest / most far-reaching
("luxe") version of design choices. Second standing directive ([USER]):
design for long-term use — the SpecTec-in-Lean tooling must be
**generically useful, not coupled to Go**; Go is the first client.

## Architecture: a three-layer trust story

- **Top — the SpecTec Go spec.** Human-readable, auditable side-by-side
  against the Go standard's prose; differentially tested against `go run`.
- **Bottom — GoCore + its semantics** (golean). Already differentially
  validated and proof-instrumented; the frontend lowering is the unproven
  gap.
- **Middle — the correspondence theorem:**
  `SpecTecSem(P) ≃ GoCoreSem(frontend(P))` for well-typed surface
  programs P. Proves the lowering sound; converts GoCore's status from
  "validated model" to "provably implements the readable spec".

The theorem is statable only because SpecTec specs get a Lean-native
meaning through this repo's deep IL embedding + semantics. The Wasm spec
+ test suite is the toolkit's permanent conformance corpus: it validates
that our *interpretation of SpecTec itself* is faithful (the OCaml
toolchain being the only oracle for "what SpecTec means") before we trust
it to give meaning to a Go spec that has no other formal referent.

**Differential structure, two legs testing different things:**
1. Lean IL semantics vs the OCaml meta-interpreter on the WASM spec +
   test suite — validates the interpreter (SpecTec fidelity).
2. The Lean interpreter running the GO spec vs `go run` on a Go corpus —
   validates the Go spec itself (no OCaml-side Go support needed).
   golean's corpus is deliberately frontend-independent canonical Go —
   reuse it, with golean's baseline discipline.

## Decisions (recommended [AGENT], ratified [USER] 2026-08-20)

**D1 — Spec coverage: full spec (syntax + static semantics + dynamics).**
Typing is authored in the spec from the start; mechanization is staged:
dynamics correspondence first, typing differential (vs go/types) second,
metatheory (progress/preservation for a standards-grade Go spec — the
far-reaching prize) third. Rationale: (a) the correspondence theorem's
honest hypothesis is spec-side well-typedness, not "whatever go/types
accepts"; (b) go/types gains a formal referent; (c) type soundness for Go
becomes possible at all. The EL prototype stress-tests BOTH idioms
(dynamics: defer/panic; typing: method sets, assignability, untyped
constants — the likeliest places SpecTec's Wasm-shaped idioms creak).

**D2 — Theorem quantification: over the SpecTec spec's own syntax
section** (the spec is the statement language). The remaining text
boundary (Go text → AST) is kept *small* — with typing in the spec,
scoping/name resolution move inside the formal spec, leaving parsing
proper — and *measured*: a standing AST-correspondence harness in the
gate exercises the boundary over the whole corpus (independent parse +
print round-trip). Explicitly NOT covered by the theorem: parsing. A full
Go text grammar in SpecTec grammar notation is deliberately out of scope
(semicolon insertion / composite-literal context-sensitivity; weak payoff
— the capped luxe choice).

**D3 — Structured mixops: vendored `backend-ast` patch in arc 2.** The
dump's `Mixop.to_string` rendering is non-injective (arc-1 finding); a
correspondence theorem must not rest on a lossy encoding. A small vendored
patch to the pinned checkout (checked in under `patches/`, applied at
setup, recorded in `baselines/upstream-pins.txt`, baseline re-pinned with
reason) makes the dump lossless: structural mixops + `LetPr` binders +
source positions. Documented divergence from upstream's dump format;
candidate for upstreaming.

**D4 — Genericity ([USER] directive).** This repo is a language-agnostic
SpecTec toolkit. Design rules:
- The core (Sexpr, IL embedding, validation, semantics, differential
  harness machinery) contains ZERO language-specific knowledge. The
  `SpecTecLean` namespace stays language-neutral.
- Language-specific value primitives (numerics, host functions) enter
  only through a declared extension interface — mirroring the OCaml
  architecture, where backend-interpreter's `numerics.ml`/`construct.ml`/
  `host.ml` are Wasm plugins outside the generic interpreter core.
- Wasm remains the permanent conformance corpus of the toolkit; Go
  artifacts (EL spec sources, Go-specific harnesses, the correspondence
  proof) live in clearly separated modules/directories — importable
  without dragging Go into the toolkit or the toolkit into Go.
- Where the correspondence proof lives (golean imports this repo, or a
  third repo imports both) is deferred; nothing built now may prejudge it.

**D5 — The EL elaborator is a named, untrusted-unverified boundary
(recommended [AGENT], accepted [USER] 2026-08-20).** The OCaml frontend
(EL parse + elaboration → IL) stays in the product path as a build tool,
NOT a trust anchor: the Lean validator re-checks every dump structurally,
and both differential legs check meaning end-to-end, so an elaborator bug
surfaces as a loud rejection or a visible divergence — never a silent
axiom. It is nevertheless the link between what humans audit (EL text)
and what the theorem consumes (IL) — the analogue of go/types in golean —
and is recorded as such. Eventual endpoint (luxe, deliberately
unscheduled): an all-Lean frontend, staged parser-then-elaboration,
gated by IL-dump BYTE-EQUALITY against the OCaml frontend (the arc-1
round-trip machinery is the ready-made comparator), and sized only after
the Go-EL prototype reveals the EL subset actually used. Permanent
regardless: the OCaml toolchain never leaves the differential gate — its
oracle role is an immovable boundary entry (CLAUDE.md).

## Staging impact

Arc 2 (binding layer + IL validation + D3 dump patch) and arc 3 (semantic
core, faithful-but-slow — [USER] ratified) are unchanged in content,
re-justified as toolkit work. The Go-EL prototype is PROMOTED: it
de-risks the central bet of the whole program (does SpecTec's idiom
express Go's dynamics AND typing) and runs right after arc 2, before or
alongside arc 3. The correspondence theorem and the full Go spec are the
long arc beyond.
