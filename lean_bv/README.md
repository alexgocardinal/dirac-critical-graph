# Lean certificate for the order-60 Dirac graph

This directory is a proof-producing certificate layer for the explicit
60-vertex Cayley graph.  It contains no `sorry` and does not import any result
from the C++/Python discovery programs.

## What Lean checks

`Dirac60/Certificate.lean` contains the complete 180-edge list and proves:

1. `puncture_balance_universal`: every proper three-colouring of `G - 0`
   assigns each of the three colours to exactly two vertices of
   `N(0) = {5,26,30,33,37,55}`.  This is an unnormalized statement.
2. `normalized_puncture_classifier`: after fixing `c(1)=0` and `c(6)=1`,
   the proper colourings of `G - 0` are exactly the 16 assignments obtained
   by independently filling the four stars at vertices `2,3,24,41`.
3. `q3_ge_two_encoded`: no three-colour assignment has at most one
   monochromatic edge.  This is the finite statement `q_3(G) >= 2` and
   immediately rules out a three-colouring after any one edge deletion.
4. `all_vertex_deletion_witnesses`: all 60 displayed positive witnesses are
   checked edge by edge.
5. `q3_le_two_witness`: one displayed assignment has exactly two
   monochromatic edges.
6. `not_three_colourable`,
   `no_single_edge_deletion_is_three_colourable`, and
   `certified_dirac_result`: proposition-level bridges from the Boolean SAT
   layer to maps `Fin 60 -> Colour3`, explicit vertex-deletion witnesses, and
   a proper `Colour4` witness.

`Dirac60/UniversalDecoupling.lean` proves the final logical glue theorem
`UniversalDecoupling.iff_ge_four`.  It takes three explicit hypotheses: the
order-4 example, existence for every `k >= 5` (the Jensen input), and the
low-chromatic obstruction.  It does **not** declare Jensen's result as an
axiom and does not pretend that the literature theorem has itself been
formalized.  Its conclusion is explicitly restricted to `k >= 2`; without
that conventional nontrivial range, the edgeless one-vertex graph creates a
vacuous `k=1` exception.  Consequently this file validates the deduction,
while the two general mathematical inputs still require citations or separate
Lean proofs.

The first three theorems use `bv_decide` on fully unrolled, quantifier-free
Boolean formulas.  `bv_decide` constructs a SAT certificate and replays it
through Lean's verified reflection pipeline.  Depending on the Lean release
and invocation mode, that pipeline may report the standard code-generator
result axiom rather than being axiom-free kernel reduction.  The source ends
with `#print axioms` commands so the build log exposes the exact answer instead
of concealing this distinction.  The positive concrete witness theorems use
`native_decide`; no UNSAT or non-colourability conclusion depends on
`native_decide`.

Three colours are encoded by two bits as `00`, `10`, `01`, with `11` ruled
out explicitly.  The balance conclusion is the conjunction of three
`exactlyTwo6` predicates, so it proves the full `2+2+2` profile, rather than
only saying that colours already present are repeated.

## Reproduce

With Lean and Lake installed:

```sh
lake update
lake build
lake exe dirac60-check
```

The source is generated mechanically from the frozen edge list and positive
witness file.  To regenerate and ensure there is no hand-copying error:

```sh
python3 generate_certificate.py
lake build
```

The pinned environment is Lean 4.19.0 with Mathlib v4.19.0. On 9 September
2026 an external `lake build` and `lake exe dirac60-check` completed
successfully after the compatibility corrections recorded in the package.
The final axiom report contains no `sorryAx`. The mathematical formulas were
also independently cross-checked against the frozen edge list and all 16
normalized punctured colourings.

The completed host-side generation audit reports:

```text
AUDIT_GENERATION_OK
edge_sha256=85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c
lean_sha256=1501ae2d85e65ba49bffb7c26d31fae384300b6c04c649accb0f2e749512a9af
n=60 m=180 degree=6
normalized_puncture_colourings=16
neighbor_profile=2+2+2
defect_witness_bad_edges=0-5,0-26
```

This audit also checks that the generated Lean source has exactly three
`bv_decide` proof invocations, contains neither `sorry` nor `admit`, embeds all
180 distinct edges, and copies all 60 positive deletion witnesses exactly.
It is a static/data audit, not evidence of successful Lean elaboration.

## Trust boundary

- Negative claims: Lean kernel, `bv_decide`'s verified SAT/reflection path,
  and any code-generator axiom printed by the pinned toolchain.
- Positive claims: Lean kernel plus the native evaluator and standard
  code-generator-result axiom used by `native_decide`.
- Input identity: the explicit edge list embedded in the source; no runtime
  file parsing is used.
- Excluded: discovery code, C++ solvers, Python solvers, and the prose report.

For the highest-assurance publication path, compile this project, retain the
Lake manifest, record toolchain hashes, and additionally export the generated
SAT proof if the selected Mathlib version exposes `bv_check`/LRAT output.
Then replay it in the tactic's kernel-checking mode and confirm from
`#print axioms` that the three negative certificate roots have the intended
axiom footprint.
