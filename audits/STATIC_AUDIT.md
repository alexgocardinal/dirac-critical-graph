# Static audit of the Dirac-60 Lean development

Date: 2026-09-09 UTC

> **Status update.** This document records an earlier source-level audit made
> before Lean was available in the audit environment. The frozen projects were
> subsequently built successfully by the author with Lean 4.19.0 and Mathlib
> v4.19.0. The later build and axiom results are recorded in
> `../verification/EXTERNAL_VERIFICATION_RECORD.md`; those results supersede
> the pre-build qualifications below.

## Verdict

The `stage3/lean_formalizer` development now has a coherent semantic proof
chain.  Its public theorem

```lean
Dirac60.order60_solution :
  FourVertexCritical Dirac60.G ∧ EdgeImmuneAtFour Dirac60.G
```

means, after unfolding the definitions, that the displayed graph is
4-colourable but not 3-colourable, every vertex puncture is 3-colourable, and
deleting any actual edge still does not make the graph 3-colourable.  The
search-tree checker has an ordinary Lean soundness proof connecting accepted
trees to quantified non-colourability; this avoids the principal semantic gap
of a bare solver-result theorem.

At the time of this static audit, the audit executor had no `lean`, `lake`,
`elan`, or `leanc`, and public toolchain acquisition was blocked. No Lean
invocation was performed in that particular environment. A subsequent build
and axiom audit succeeded; see the status update above.

If the project compiles as written, its headline result will inherit the
documented `native_decide` code-generator result axiom (normally printed as
`Lean.ofReduceBool` in the relevant versions).  It must therefore be described
as Lean-native-checked, not as an axiom-free kernel computation.

## Environment and reproduction

The formalizer project now pins both Lean and Mathlib to `v4.19.0`:

```text
leanprover/lean4:v4.19.0
mathlib4 tag v4.19.0
```

On a machine with Elan/Lake and network access, run:

```bash
cd stage3/lean_formalizer
lake update
lake build
lake env lean AxiomAudit.lean
python3 replay_certificates.py
sha256sum --check SHA256SUMS
```

Preserve `lake-manifest.json`, the complete build log, `lean --version`,
`lake --version`, and all `#print axioms` output.  The current latest stable
Lean observed during this audit was 4.33.1, but changing from the project's
pinned 4.19.0 before the initial reproducible build would introduce a second
variable.  First compile the frozen pin; then port and separately audit on a
current release.

## Semantic architecture reviewed

The proof path in `stage3/lean_formalizer` is:

1. `BalancedPuncture.lean` defines proposition-level proper colourings,
   vertex punctures, edge deletions, 4-vertex-criticality, and edge immunity.
2. `Dirac60.lean` defines the 60-vertex Cayley graph, positive colouring
   witnesses, a list-colouring problem, an inductive search tree, and
   `valid_no_extension`, the generic soundness theorem for accepted trees.
3. `Dirac60Certificates.lean` contains 21 generated finite trees: 18 exclude a
   specified colour occurring at exactly one specified neighbour of zero, and
   three exclude a specified colour being absent from that neighbourhood.
4. `Dirac60Result.lean` native-checks tree validity, uses the generic soundness
   proof to obtain proposition-level UNSAT facts, derives two neighbours of
   every colour around the root, transports this fact by Cayley translations,
   and applies the abstract balanced-puncture theorem.
5. The numerical `exact_two_two_two_profile` theorem combines the lower bound
   of two per colour with the native-checked degree-six fact.
6. `UniversalDecoupling.lean` proves the elementary arithmetic closure of the
   all-`k` classification while taking the order-four existence statement,
   Jensen's `k >= 5` input, and the low-chromatic obstruction as explicit
   hypotheses.  It declares none of those external inputs as axioms.

This chain is mathematically sound in static review.  In particular:

- `Valid` is structurally recursive on an inductive tree, so cyclic or
  out-of-range child pointers are not representable in Lean.
- At every branch, all three values of `Fin 3` are covered.  A `.closed` child
  is accepted only when the corresponding `Compatible` premise is false.
- `valid_no_extension` follows any hypothetical total proper colouring down
  its compatible branch and derives a contradiction at a closed leaf.
- The list-problem-to-punctured-colouring lemmas establish a real semantic
  bridge; the Python generator is not assumed sound.
- `ProperAfterEdge` removes both orientations of the unordered edge, and
  `EdgeImmuneAtFour` quantifies only over actual edges.
- `FourVertexCritical` is equivalent to the required chromatic statement in
  this setting: 4-colourability plus non-3-colourability gives chromatic number
  four, while each puncture's 3-colourability gives a strict drop.

## Concrete data checks performed outside Lean

These checks are error-detection aids, not substitutes for the Lean build.

- Recomputed the adjacency predicate directly from the group law and
  connection set in `Dirac60.lean`.
- Obtained exactly 180 undirected edges, degree set `{6}`, no loops, and root
  neighbourhood `{5,26,30,33,37,55}`.
- Compared those 180 edges with
  `Dirac_k4_order60_solution/candidate60.edgelist`: symmetric difference zero.
- Frozen edge-list SHA-256:
  `85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c`.
- Replayed all 21 JSON trees: 35,967 reachable branch nodes; all cases passed.
  The independent red-team checker additionally verifies exact masks, case
  coverage, postorder indices, and every possible branch.
- The generated Lean tree file has 35,967 balanced `.branch` expressions;
  maximum certificate depth is 57.

## Static Lean/API risks remaining

No definite logical error remains after two reported proof errors were fixed
(the looplessness contradiction and translation injectivity at the puncture).
The following are execution risks that only a real build can settle:

1. **Elaboration and native compilation load.**
   `Dirac60Certificates.lean` is about 1 MB and contains lines up to roughly
   177 kB.  The 35,967-node nested terms are shallow enough (depth at most 57)
   to be plausible, and the project raises `maxRecDepth`, but parser,
   elaborator, or native-code memory/time must be measured.
2. **Decidability synthesis for `Valid`.**
   Each of the 21 replay declarations asks `native_decide` to synthesize and
   execute decisions containing finite universal quantifiers over `Fin 60`.
   Mathlib should provide the needed finite instances, but this was not tested
   under the pinned version.
3. **Tactic/API drift.**
   The sources rely on `fin_cases`, `native_decide`, `Function.update_noteq`,
   `Bool.eq_false_of_not_eq_true`, and Finset cardinality lemmas as they existed
   in Mathlib 4.19.  Their exact elaboration cannot be certified statically.
4. **Build metadata.**
   `lake-manifest.json` is necessarily absent until `lake update` succeeds.
   A release should include it and should not silently resolve Mathlib from a
   moving branch.

Source scans found no `sorry`, `admit`, user `axiom`, `unsafe`, or `opaque`
declarations in the formalizer's `.lean` files.

## Trust-boundary audit

`BalancedPuncture.twoPerColour_edgeImmune` and
`Dirac60.valid_no_extension`, and
`UniversalDecoupling.iff_ge_four` are ordinary proof terms.  The concrete premises
feeding the final theorem are not all ordinary kernel reductions:

- 21 tree-validity facts use `native_decide`;
- graph symmetry and looplessness use `native_decide`;
- concrete positive colouring witnesses use `native_decide`;
- translation identity, injectivity, and adjacency preservation use
  `native_decide`;
- neighbour degree six uses `native_decide`.

Thus `order60_solution` inherits native evaluator/compiler trust.  The README
now says this accurately, and `AxiomAudit.lean` prints axioms for the abstract
edge lemma, checker soundness theorem, exact profile, and headline result.
After a successful build, inspect rather than predict the exact output.

For a stronger endpoint on a current Lean release, replace the final tree
validity checks with `decide_cbv`, `by decide`/kernel reduction, or generated
explicit proof terms, and rerun `#print axioms`.  `decide_cbv` is the documented
route that creates proofs by propositional rewriting without adding the
compiler-result axiom.  `bv_decide`, `native_decide`, and (without an explicit
axiom audit) `bv_check` must not be advertised as wholly kernel-computational.

## Audit of `stage3/lean_certificate`

The separate bit-vector/Boolean candidate was also checked statically and at
the data level:

- its embedded edges match the frozen 180-edge graph;
- all 60 deletion witnesses have length 60, values in `{0,1,2}`, and are
  proper away from their deleted vertex;
- the displayed defect colouring has precisely the two conflicts
  `{0,5}` and `{0,26}`;
- its unrolled whole-graph formula contains the correct 180 edge pairs, and
  its punctured formula contains the correct 174 non-root edges.

Its main remaining execution risk is whether `bv_decide` in pinned Lean 4.19
will unfold the custom recursive Boolean list helpers.  More importantly, it
must retain its newer proposition-level bridges and `#print axioms` commands;
earlier revisions duplicated graph data between formulas and witness checks
without a theorem identifying the two representations.  As with the
search-tree project. This pre-build audit's condition was subsequently met:
both projects built successfully under Lean 4.19.0; see
`../EXTERNAL_VERIFICATION_RECORD.md`.

## Scope of the universal statement

The order-60 theorem proves the missing existence case at chromatic number
four.  It does not by itself formalize the all-`k` graph theory.  The new
`UniversalDecoupling.iff_ge_four` theorem is an honest **conditional closure**:
it derives the biconditional from explicit parameters representing the
order-four result, Jensen's theorem, and the low-colour obstruction.  The valid universal
classification is existential in `k` (with `k >= 2`, or with an explicit
nonempty-edge condition), not the false pointwise biconditional for each graph.
The mathematical sufficiency for `k >= 5` still comes from Jensen's published
theorem, and a full Lean proof would have to formalize Jensen's construction
or expose it as an explicit hypothesis.  For example, `K4` refutes the
pointwise reading because it is 4-vertex-critical but its edges are critical.
