# Lean 4 certificate package for the order-60 graph

This directory formalizes the explicit order-60 Cayley graph and the
balanced-puncture proof of its critical/edge-immune properties.

## Main statements

- `BalancedPuncture.twoPerColour_edgeImmune` is the general theorem: if every
  proper 3-colouring of every vertex-puncture uses each colour on at least two
  neighbours of the puncture, then deleting an edge never makes the graph
  3-colourable.
- `Dirac60.exact_two_two_two_profile` states that every proper 3-colouring of
  every puncture of the explicit graph has neighbour profile exactly 2+2+2.
- `Dirac60.order60_solution` states
  `FourVertexCritical G ∧ EdgeImmuneAtFour G`.
- `UniversalDecoupling.iff_ge_four` proves the final if-and-only-if arithmetic
  closure while keeping the `k >= 5` construction theorem and the `k <= 3`
  obstruction as explicit hypotheses. It does not silently assume Jensen.

There are no `sorry`, `admit`, or user-declared axioms in these sources.

## Certificate design

`generate_certificates.py` independently searches 21 list-colouring
instances:

- 18 instances rule out a colour occurring exactly once on `N(0)` (six
  possible neighbours times three colours);
- three instances rule out a colour missing from `N(0)`.

The generated forest has 35,967 nodes. `Dirac60.Valid` recomputes every
allowed branch, and `Dirac60.valid_no_extension` proves the checker sound for
arbitrary list-colouring problems. Thus the generated search program is not
in the logical trust base.

## Build and audit

With Lean and network access available:

```sh
lake update
lake build
lake env lean AxiomAudit.lean
python3 replay_certificates.py
sha256sum --check SHA256SUMS
```

The package is pinned to Lean/mathlib `v4.19.0`.

## Exact trust boundary

The current replay and concrete finite graph facts use `native_decide`. In
Lean, this avoids infeasible kernel reduction by compiling a Boolean decision
procedure. It therefore relies on Lean's native code generator and introduces
the native-decision result axiom (`Lean.ofReduceBool` in the relevant Lean
versions). The abstract checker-soundness and balanced-puncture lemmas are
ordinary proof terms, but the final theorem inherits the native-decision trust
boundary through certificate validation, witness checking, and finite Cayley
identities.

On 9 September 2026 this project completed an external `lake build` with Lean
4.19.0 and Mathlib v4.19.0. `AxiomAudit.lean` reported no `sorryAx`; the final
theorem `Dirac60.order60_solution` depends on `[propext, Classical.choice,
Lean.ofReduceBool, Quot.sound]`. The independent replay passed all 21 cases
and all 35,967 nodes, and the corrected `SHA256SUMS` manifest passed in full.

The frozen edge-list identity is
`85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c`.
