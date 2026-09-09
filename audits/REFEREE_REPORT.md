# Skeptical referee report for the Lean result

## Bottom line

The finite order-60 claim should be exposed in Lean at the semantic level as

```lean
FourColorable G60
  ∧ (¬ ThreeColorable G60)
  ∧ (∀ v, ThreeColorableAwayVertex G60 v)
  ∧ (∀ u v, Adj G60 u v → ¬ ThreeColorableAwayEdge G60 u v)
```

or by an equivalent theorem from which these four conjuncts are proved.  This
is enough to conclude that `chi(G60) = 4`, every vertex deletion has chromatic
number 3, and every single-edge deletion still has chromatic number 4.

A theorem merely saying that a bespoke Boolean search routine returned
`false` is not yet a graph-colouring theorem.  The development must contain a
proved soundness bridge from every accepted search certificate to the
quantified proposition `¬ ∃ c : V → Fin 3, Proper ... c`.

The proposed “Universal Decoupling Theorem” is true only after two corrections:

1. it must be an **existence classification by chromatic number**, not a
   pointwise characterization of every graph; and
2. either the graph must be required to have an edge or the parameter must be
   restricted to `k ≥ 2`, because `K₁` is a vacuous exception under the usual
   convention `chi(empty) = 0`.

The new Lean calculation supplies the previously open `k = 4` case.  It does
not by itself formalize the `k ≥ 5` cases, which use Jensen's published theorem.

## Recommended semantic definitions

For a custom finite representation, definitions along the following lines are
hard to misread:

```lean
abbrev Vertex := Fin 60
abbrev Color3 := Fin 3
abbrev Color4 := Fin 4

def Proper (adj : Vertex → Vertex → Prop) (c : Vertex → Fin q) : Prop :=
  ∀ ⦃u v⦄, adj u v → c u ≠ c v

def ProperAwayVertex (adj : Vertex → Vertex → Prop)
    (x : Vertex) (c : Vertex → Fin q) : Prop :=
  ∀ ⦃u v⦄, adj u v → u ≠ x → v ≠ x → c u ≠ c v

def ProperAwayEdge (adj : Vertex → Vertex → Prop)
    (x y : Vertex) (c : Vertex → Fin q) : Prop :=
  ∀ ⦃u v⦄, adj u v →
    ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) → c u ≠ c v
```

If the checker uses `Bool`, the public definitions can replace each
proposition with a test equal to `true`, but the equivalence with the
mathematical predicate must be proved.  In particular:

* vertex deletion must omit edges incident at **either** endpoint;
* edge deletion must omit both orientations of the unordered edge;
* “no critical edge” should quantify only over actual edges;
* a 4-colouring witness and a proof of non-3-colourability are both required;
* positive 3-colourings after vertex deletion prove only `chi ≤ 3`; exact
  equality follows because a 2-colouring of `G-v` could be extended with a
  third colour at `v`, contradicting non-3-colourability of `G`;
* non-3-colourability of `G-e` plus the displayed 4-colouring of `G` proves
  `chi(G-e)=4`, since restriction preserves properness.

It is acceptable to model `G-v` on the original 60-element type with `v`
isolated, but this convention must be stated.  It is colourability-equivalent
to induced deletion here; using `ProperAwayVertex` avoids the issue entirely.

## The most compact negative certificate

The punctured-colouring argument can reduce the negative workload.  One clean
certificate family proves:

1. `G60` is not 3-colourable; and
2. for every proper 3-colouring of `G60-0`, no colour is absent from the six
   neighbours of 0; and
3. in such a colouring, no colour occurs exactly once there.

For (3), the generated certificate family has 18 cases: select one of the six
neighbours `s` and one of three colours `a`, impose `c(s)=a`, and forbid `a`
at the other five neighbours.  Unsatisfiability of all cases says that every
colour used by a neighbour is duplicated.  Three further cases forbid each
colour at all six neighbours, establishing (2).  Since six positions are
partitioned among three present, nonsingleton colour classes, their sizes are
exactly `2+2+2`; this also supplies (1), because the colour of vertex 0 would
conflict with a neighbour in any proposed colouring of the whole graph.

Then a hypothetical 3-colouring of `G60-0s` must have `c(0)=c(s)`; otherwise
it would colour `G60`.  The other five neighbours avoid `c(0)` because their
edges to 0 remain, so `s` would be the unique neighbour of that colour,
contradicting (2).  Left translation transports this from the six edges at 0
to all edges.

Important: the 18 “no unique neighbour colour” certificates do **not** by
themselves prove that `G60` is non-3-colourable.  They become sufficient only
when combined with the three no-missing-colour certificates (or with a
separate whole-graph unsatisfiability certificate).

## Certificate-checker obligations

For a DPLL/list-colouring tree, a kernel theorem should establish something
equivalent to

```lean
theorem checkCert_sound
    (h : checkCert adj active masks cert = true) :
    ¬ ∃ c, ExtendsMasks active masks c ∧ ProperOn active adj c
```

The checker must independently reject all of the following:

* a branch vertex outside `Fin 60` or outside the active set;
* branching on an already assigned vertex;
* a missing child for a colour that is currently possible;
* a supplied child for a colour that is currently impossible, if the soundness
  proof assumes exact branching;
* a child that does not extend the parent assignment with the claimed colour;
* cyclic, forward, or out-of-range child indices;
* a leaf that is not genuinely contradictory;
* success with uncoloured vertices remaining;
* a mask value containing colour bits outside `{0,1,2}`.

Using a decreasing fuel/index discipline is a clean way to exclude cycles.
The Python generator is not trusted; only the Lean checker and its soundness
proof may carry logical weight.

## Graph-identity obligations

The public graph should be the coordinate Cayley graph on
`Fin 12 × Fin 5`, or a transparently listed 180-edge graph.  If both are
included, prove their adjacency predicates extensionally equal in Lean.

For the coordinate presentation, check in Lean (or make definitional) that

```text
(e,i) * (f,j) = (e+f mod 12, i + 2^e*j mod 5)
S = {(1,0),(11,0),(5,1),(7,2),(6,0),(6,3)}.
```

The adjacency predicate must be symmetric and irreflexive.  The six generator
values must be distinct and nonidentity.  The inverse pairs are
`(1,0)↔(11,0)`, `(5,1)↔(7,2)`, while `(6,0)` and `(6,3)` are involutions.
If symmetry is used to reduce 180 edge checks to six, the Lean proof must show
that left translations preserve adjacency and carry every edge to one incident
with 0.  External hash agreement is useful provenance, but not a substitute
for equality of the graph used by the theorem and the advertised graph.

## `native_decide`, `bv_decide`, and the trust boundary

Lean's own current reference manual is explicit:

* `native_decide` trusts the Lean compiler and introduces a new axiom;
* `bv_decide` obtains and checks a SAT certificate, but its current frontend
  also trusts the code generator and adds an axiom asserting the native
  computation result;
* `decide_cbv` produces a proof by propositional rewriting and does not require
  trust in the code generator (apart from Lean's standard logical axioms).

Therefore:

* a result ending in `native_decide` or `bv_decide` is reasonably described as
  **Lean-based** or **Lean native-checked**, but not as a computation whose
  truth was reconstructed entirely by kernel reduction;
* a certificate accepted by a proved checker, with the final closed check
  discharged by `decide_cbv`, `by decide`, `rfl`, or an explicit proof term,
  is the preferred kernel-checked result;
* `bv_check` makes the external LRAT replayable but, in current Lean, does not
  automatically remove the code-generator axiom from the trust base;
* an untrusted tactic may freely generate a large proof term: this is safe if
  the kernel checks that proof term and no result axiom is introduced.

Every delivered build should include the output of

```lean
#print axioms Dirac60.candidate60_result
```

and analogous commands for the constituent negative-certificate theorems.
Any occurrence of `Lean.ofReduceBool` (or a freshly generated result axiom)
must be disclosed.  Also scan the source and dependencies for `sorry`,
`admit`, user-declared `axiom`, and semantic definitions marked `opaque`.

Even an axiom-free Boolean theorem can have a semantic gap.  For example,
`theorem searchSaysNo : mySearch = false := rfl` says nothing about graph
colouring until `mySearch = false → ¬ ∃ c, Proper c` is proved.

## Correct universal theorem statement

One robust mathematical statement is

```text
For every natural k,
  (there exist n and a finite simple graph G on Fin n such that
     G has at least one edge,
     chi(G)=k,
     every vertex deletion lowers chi, and
     every single-edge deletion preserves chi)
  iff 4 ≤ k.
```

Equivalently, quantify only over `k ≥ 2` and omit the explicit `HasEdge`
condition.  Do not state

```text
Decoupled(G) ↔ 4 ≤ chi(G).
```

That pointwise formula is false: `K₄` has chromatic number 4 and is
vertex-critical, but every edge of `K₄` is critical.  `K₄` plus an isolated
vertex is an even simpler counterexample to the implication from chromatic
number alone, since it is not vertex-critical.

The low-colour necessity is elementary for non-vacuous graphs.  A
2-vertex-critical graph is `K₂`, whose edge is critical.  A
3-vertex-critical graph is an odd cycle, every edge of which is critical.
For sufficiency, the new order-60 graph gives `k=4`, while Jensen (2002) gives
all `k≥5` (and Skottova--Steiner give stronger `(k,r)` results for `k≥5`).

Thus it is accurate to say that the new result *completes the mathematical
existence classification when combined with Jensen's theorem*.  It is not
accurate to call the whole classification Lean-formalized unless Jensen's
general construction and the `k≤3` arguments have also been formalized.  In a
Lean file, Jensen may be exposed as an explicit hypothesis and the final
statement proved conditionally; declaring it as an axiom must be visible in
`#print axioms`.

## Required release audit

Before calling the artifact a Lean proof, record:

1. the pinned Lean version and exact `lake-manifest.json`;
2. a clean `lake build` transcript;
3. `#print axioms` output for every top-level advertised theorem;
4. a source scan for `sorry|admit|axiom|unsafe|native_decide|bv_decide`;
5. an independent check that the Lean adjacency relation yields exactly the
   180 edges in `candidate60.edgelist` and its advertised SHA-256;
6. theorem names and their fully elaborated types;
7. whether the universal theorem is formalized, conditional on Jensen, or only
   stated in the accompanying paper.

## Static audit findings in the current workspace

These findings concern draft sources observed before any Lean toolchain was
available; they should be rechecked after regeneration.

* `stage3/lean_formalizer/certificates.json` currently contains 21 proof trees:
  18 no-unique-neighbour-colour instances and three no-missing-colour
  instances.  An independently written structural traversal checked all
  35,967 tree nodes, every mask, every possible branch, strict decreasing
  child indices, reachability, and exact case coverage.  See
  `independent_certificate_audit.py` and its log in this directory.  This is
  useful error detection but does not replace Lean's checker-soundness proof.
* The initial draft of `BalancedPuncture.lean` used lowercase ASCII `and`,
  `or`, `not`, and Boolean inequality `!=` where proposition-level
  `And`/`Or`/`Not` and `≠` are required by the subsequent proofs.  This is a
  likely parse/type failure and was reported to its author.
* The initial `stage3/lean_certificate` normalized-classifier theorem had a
  false right-to-left direction: the four free positions were constrained by
  negating one colour predicate, which also admitted the invalid bit code
  `11`.  This was reported and the author stated that it was corrected with
  positive domain disjunctions.
* That `lean_certificate` draft directly proved useful universal Boolean
  formulas with `bv_decide`, but did not yet contain a proposition-level
  theorem about colourings, chromatic number, or graph deletion.  Its
  `q3_le_two_witness` checked only the number of conflicts and should also
  check length 60 and validity of every displayed colour code.
* Neither draft had been compiled in the provided executor.  A source file,
  even a plausible one, must not be described as a verified Lean result until
  the pinned toolchain accepts it and the axiom report is recorded.

### Later static pass over `Dirac60Result.lean`

The completed proof-tree draft has a sound high-level chain:

```text
tree validity
  -> no colouring of each list instance
  -> every punctured colouring has every colour twice at the root
  -> Cayley translation gives the condition at every puncture
  -> balanced-puncture lemma
  -> 4-vertex-critical and single-edge-stable.
```

The `Valid` predicate is recursively defined on an inductive tree, not on
unchecked node indices, so cyclic certificates cannot be represented.  Its
three implications cover all values of `Fin 3`.  The accompanying soundness
proof correctly shows that any total colouring extending a state would select
one of those branches.  This part survived static logical review.

Two likely elaboration errors were found and subsequently corrected by the
author: use of looplessness as though an equality proof were a function, and
application of translation injectivity before rewriting `r` as the translate
of zero.  The final `2+2+2` proof is mathematically sound: two certified
neighbours per colour give three lower bounds of two, while the three colour
classes disjointly partition a degree-six neighbourhood.

This paragraph originally preceded execution of the Lean development. The 21
tree-validity declarations use `native_decide`, so their logical chain includes
the native code-generator result axiom. The frozen project was subsequently
built successfully with Lean 4.19.0 and Mathlib v4.19.0, and its axiom transcript
was recorded in `../verification/EXTERNAL_VERIFICATION_RECORD.md`. Independent
public reproduction and expert review are still required.
