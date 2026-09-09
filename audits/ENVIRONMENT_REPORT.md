# Lean environment and certificate architecture for the Dirac-60 graph

Date of inspection: 2026-09-09 UTC.

## Executable environment result

There is no Lean toolchain in this executor.  All four commands are absent:

```text
lean=
lake=
elan=
leanc=
```

Searches under `/opt`, `/usr/local`, and `/root` found no Lean executable,
`libLean.so`, Mathlib checkout, Lake cache, or Elan installation.  Consequently
there is no installed version to report and no Lean theorem can honestly be
marked as compiled in this environment.

The attempted public acquisition routes were also unavailable from the
terminal:

* `https://github.com/leanprover/lean4.git`: HTTP 403;
* `https://releases.lean-lang.org/...`: HTTP 403;
* SourceForge's Lean mirror: HTTP 403;
* the configured Git proxy requires credentials that are unavailable in this
  session.

The checked shell commands were:

```bash
command -v lean
command -v lake
command -v elan
command -v leanc
lean --version
lake --version
find /opt /usr/local /root -type f \
  \( -name lean -o -name lake -o -name elan -o -name libLean.so \)
```

Thus `Probe.lean` in this directory is an **unexecuted probe input**, not a
verification log.  Once a toolchain is available, run:

```bash
cd stage3/lean_environment
lake env lean Probe.lean
lake build
```

## Recommended pinned toolchain

Use Lean **4.33.1**, pinned by the adjacent `lean-toolchain` file:

```text
leanprover/lean4:v4.33.1
```

This is the latest stable release visible on 2026-09-09 (4.34.0 was still an
RC).  More importantly, 4.33.1 contains kernel and runtime soundness fixes and
is explicitly recommended over 4.33.0 by the Lean release notes.

The primary certificate should initially be **Std-only**, importing
`Std.Tactic.BVDecide`; Mathlib is not required for the expensive finite fact.
That makes the computational core smaller and avoids instability in graph API
names.  A second, thin Mathlib module can translate the checked predicates to
`SimpleGraph.Colorable` and `SimpleGraph.chromaticNumber`.

## Why direct `native_decide` is the wrong negative proof

The proposition

```lean
∃ c : Fin 60 → Fin 3, Proper c
```

has a standard finite `Decidable` instance, but direct evaluation can enumerate
up to `3^60` functions.  `native_decide` only makes that enumeration native; it
does not turn it into a constraint-solving algorithm.  It is appropriate for
the positive, fully explicit checks (180 edges, 60 transported witnesses), not
for non-3-colourability.

The negative fact should be encoded as a quantifier-free bit-vector formula and
discharged by Lean's SAT integration.

## Recommended certificate architecture

### 1. A 120-bit colour assignment

Represent a putative 3-colouring by `x : BitVec 120`.  Vertex `v` receives the
two bits at offsets `2*v` and `2*v+1`.  Reject code `11`; codes `00`, `01`, and
`10` are colours 0, 1, and 2.

Generate the following Boolean expressions from the frozen 180-edge list.  The
generator should unroll the lists into expressions so that `bv_decide` sees a
pure `QF_BV` formula rather than an opaque graph-search routine.

```lean
def valid3 (x : BitVec 120) : Bool := ...       -- all 60 codes != 3
def same (x : BitVec 120) (u v : Nat) : Bool := ...
def conflicts (x : BitVec 120) : BitVec 8 := ...
```

`conflicts` is the sum of 180 zero-extended one-bit equality indicators.  Eight
bits cannot overflow because the maximum is 180.

The decisive theorem is one SAT query:

```lean
theorem defect_ge_two (x : BitVec 120) :
    valid3 x = true → (2#8).ule (conflicts x) = true := by
  bv_decide
```

This is stronger and cleaner than formalizing 181 separate UNSAT instances. It
says every 3-colour map has at least two monochromatic edges.  Hence the graph
is not 3-colourable and deleting any one edge still leaves it non-3-colourable.

Run `bv_decide?`, retain the emitted LRAT file, and replace the tactic in the
frozen release by `bv_check "defect_ge_two.lrat"`.  This makes replay
independent of the external SAT solver.  Also retain a SHA-256 digest of the
edge file, the generated Lean source, and the LRAT file.

### 2. Balanced-puncture theorem

Define `properAway0 x` by unrolling the 174 edges not incident with vertex 0.
For the six neighbours `[5,26,30,33,37,55]`, sum equality indicators for each
of the three colour codes into a 3-bit counter.  Then define

```lean
def balancedAt0 (x : BitVec 120) : Bool :=
  countNeighbourColour x 0 == 2#3 &&
  countNeighbourColour x 1 == 2#3 &&
  countNeighbourColour x 2 == 2#3

theorem balanced_puncture (x : BitVec 120) :
    valid3 x = true →
    properAway0 x = true →
    balancedAt0 x = true := by
  bv_decide
```

This version avoids colour normalization entirely and proves the invariant
statement directly.  A separate normalized rigidity theorem can assert the
fixed template from the C++ enumeration if desired:

```text
-0**21102120110012022002*1110202021202100*022201111120202021
```

with free vertices `2,3,24,41`.  The balanced theorem is sufficient for the
mathematical argument; proving exact cardinality 16 is optional.

### 3. Positive witnesses

Pack the supplied punctured colouring into a `BitVec 120`.  With the deleted
vertex arbitrarily assigned 0 its value is

```text
0x6222554a8418988855828905261620
```

Assigning vertex 0 colour 1 changes the last hexadecimal digit to 1 and creates
exactly the two conflicts `{0,5}` and `{0,26}`:

```text
0x6222554a8418988855828905261621
```

Use `decide` (preferred if it performs acceptably) or `native_decide` to check:

* the displayed assignment is proper away from 0;
* the second assignment is valid and has exactly two conflicts;
* the Cayley edge generator equals the frozen 180-edge list;
* the graph has 60 vertices and every vertex has degree 6;
* translating the base punctured colouring gives a proper colouring after each
  of the 60 possible vertex deletions.

These are small concrete evaluations.  If `native_decide` is used, state its
trust boundary: it adds the Lean compiler and `@[implemented_by]` code to the
trusted base.  The small positive checks can instead be structured to close by
`decide +kernel` or `cbv`, eliminating that extra dependency.

### 4. Proposition-level bridge

First state the certified result using small explicit predicates:

```lean
def ThreeColorable : Prop :=
  ∃ x : BitVec 120, valid3 x = true ∧ conflicts x = 0

def ThreeColorableAfterDeletingEdge (e : Edge) : Prop := ...
def ThreeColorableAfterDeletingVertex (v : Fin 60) : Prop := ...
```

Prove:

```lean
¬ ThreeColorable
∀ v, ThreeColorableAfterDeletingVertex v
∀ e, ¬ ThreeColorableAfterDeletingEdge e
```

Then add a Mathlib-facing module defining `G60 : SimpleGraph (Fin 60)`.  Build
actual `G60.Coloring (Fin 4)` and deletion colourings via
`SimpleGraph.Coloring.mk`, and use the current API:

* `SimpleGraph.Colorable`;
* `SimpleGraph.chromaticNumber`;
* `SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable`.

Keep this bridge outside the finite SAT core.  It is ordinary theorem proving
and can change with Mathlib without invalidating the certificate.

## Expected feasibility

The proposed SAT instance has 120 input bits, 60 validity constraints, and 180
edge equalities plus small adder circuitry.  This is tiny for modern SAT.  The
existing exact C++ normalized puncture search uses only 99 search nodes, which
strongly suggests that both `balanced_puncture` and `defect_ge_two` should solve
quickly once bit-blasted.  The LRAT proof size is unknown until the actual run,
so it must be measured rather than promised.

The `Probe.lean` file contains a six-line smoke test for both tactics.  It was
not runnable here because the required binaries are absent.

## Trust statement to use in the deliverable

Do not describe an unrun `.lean` file as a Lean proof.  The accurate status
levels are:

1. **Lean source prepared, not checked**: no successful Lean invocation.
2. **Lean-checked with `native_decide`/`bv_decide`**: theorem accepted, with
   the documented compiler/code-generator trust axiom.
3. **Frozen SAT replay with `bv_check`**: external solving removed from replay;
   LRAT is verified inside Lean, while the documented code-generator trust
   boundary remains.
4. **Independent-kernel replay**: strongest publication target, after checking
   the resulting environment with another Lean kernel implementation where
   supported.

Every released module should end with `#print axioms` for its headline
theorems, and its build log should be retained.  In particular, neither
`bv_decide` nor `bv_check` should be advertised as completely kernel-only:
current Lean documentation states that the bit-vector integration trusts the
code generator and adds an axiom asserting the computed result.  For an
axiom-free computational endpoint, investigate a small verified search-tree or
resolution checker evaluated by `decide_cbv`.  The normalized puncture search
has only 99 nodes, so a compact checked tree may be practical; unlike
`native_decide`, `decide_cbv` constructs proofs by propositional rewriting and
does not depend on compiler correctness.

## Scope warning for the proposed Universal Decoupling Theorem

Formalizing this 60-vertex graph proves existence at chromatic number 4.  It
does **not by itself** prove existence for every chromatic number `k >= 4`.
That universal sufficiency direction needs a separate closure construction
which raises the chromatic number while preserving both vertex-criticality and
edge-deletion immunity.  Joining with a clique does not work: edges of the
clique become critical.  The Lean project should therefore keep the concrete
`k=4` theorem separate from any claimed all-`k` theorem until such a closure
lemma has been proved.

At the ordinary-mathematics level, the correctly quantified universal theorem
*does* follow by combining the new `k=4` example with Jensen's published 2002
existence theorem for every `k >= 5`; Skottova--Steiner's 2026 introduction
states this explicitly.  The statement must quantify over `k` and assert the
existence of a suitable graph.  The per-graph biconditional

```text
(G is vertex-critical and edge-immune) iff chi(G) >= 4
```

is false (for example, `K4` has chromatic number 4 but its edges are critical).
An honest Lean theorem for all `k` therefore either has to formalize Jensen's
construction/proof, or take the published `k >= 5` theorem as an explicit
assumption.  The necessity for `k < 4` follows from the classification of
3-vertex-critical graphs as odd cycles, together with the elementary cases
`k <= 2`.
