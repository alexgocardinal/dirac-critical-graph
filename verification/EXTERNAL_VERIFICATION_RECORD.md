# External Lean 4.19 verification record

Date: 9 September 2026

Toolchain reported by Lake: Lean 4.19.0 with Mathlib v4.19.0.

## Compact certificate

`lake build` completed successfully. `lake exe dirac60-check` printed:

```text
Dirac60 Lean certificate elaborated successfully.
edges: 180
all concrete vertex witnesses valid: true
displayed three-colour defect: 2
```

The final compact theorem `Dirac60.certified_dirac_result` reported the axiom
footprint `[propext, Classical.choice, Lean.ofReduceBool, Quot.sound]`, with no
`sorryAx`.

## Independent structured certificate

`lake build` completed successfully. `lake env lean AxiomAudit.lean` reported:

```text
BalancedPuncture.twoPerColour_edgeImmune: [propext]
Dirac60.valid_no_extension: [propext, Quot.sound]
Dirac60.exact_two_two_two_profile:
  [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
Dirac60.order60_solution:
  [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
UniversalDecoupling.iff_ge_four: [propext, Quot.sound]
```

No reported theorem depends on `sorryAx`.

The independent Python replay reported 21 passing cases and 35,967 passing
nodes. It reproduced:

```text
EDGE_SHA256 85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c
CERT_SHA256 5959d3f0943bba98e2278ae567f7bbe2a406e41f7ce2015fa6e0101b9449e195
```

The corrected structured `SHA256SUMS` manifest reported every file `OK`.

## Exact conclusion and boundary

The explicit order-60 graph theorem is Lean-checked: the formal statement is
`Dirac60.order60_solution : FourVertexCritical G ∧ EdgeImmuneAtFour G`.
Concrete finite evaluation and certificate validation rely on
`Lean.ofReduceBool`, so the practical trust base includes Lean's native code
generation path. The abstract balanced-puncture theorem itself has the smaller
footprint `[propext]`.

`UniversalDecoupling.iff_ge_four` checks the logical deduction conditionally.
It does not formalize Jensen's published construction for every `k >= 5`;
that literature result remains an explicit hypothesis. Independent public
reproduction and peer review remain necessary for publication-level acceptance.
