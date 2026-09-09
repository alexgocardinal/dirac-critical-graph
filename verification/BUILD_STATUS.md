# Build and verification status

Date: 9 September 2026

## Passed in this workspace

- Graph structure: 60 vertices, 180 distinct edges, simple, connected,
  6-regular, and Cayley left translations verified.
- Exact colourability replay: the graph is not 3-colourable; all 60
  vertex-deleted graphs are 3-colourable; none of the 180 single-edge-deleted
  graphs is 3-colourable.
- Compact-certificate generation audit: PASS.
- Independent search-tree replay: all 21 cases and all 35,967 nodes PASS.
- Frozen edge-list SHA-256:
  `85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c`.
- Compact Lean source SHA-256:
  `1501ae2d85e65ba49bffb7c26d31fae384300b6c04c649accb0f2e749512a9af`.
- Static scans found no `sorry`, `admit`, user-declared axiom, `unsafe`, or
  `opaque` escape in the substantive Lean sources.

## Completed externally with Lean 4.19.0

- Compact `lean_bv` project: `lake build` completed successfully.
- Compact executable: `lake exe dirac60-check` reported 180 edges, all
  concrete vertex witnesses valid, and displayed three-colour defect 2.
- Structured `lean_search_tree` project: `lake build` completed successfully.
- `AxiomAudit.lean`: no theorem reported `sorryAx`.
- Independent replay: 21 cases and 35,967 nodes passed.
- Corrected structured `SHA256SUMS`: every entry reported `OK`.

## Not formalized end to end

- Formalization of Jensen's theorem for every chromatic number `k>=5`.
- Independent public reproduction or peer review.

The order-60 `k=4` result is Lean-checked within the printed trust boundary.
The universal logical glue theorem also compiles, but retains Jensen's `k>=5`
existence result and the low-chromatic obstruction as explicit hypotheses.

## External build feedback and revision 2

The first Lean 4.19 external build reached all substantive generated formulas,
but exposed three elaboration failures in `lean_bv/Dirac60/Certificate.lean`:
a `simp` step limit and two brittle proposition-level normalization bridges.
Revision 2 raises the simplifier budget for `q3_ge_two_encoded`, discharges the
valid-colour premise separately in `no_at_most_one_bad_edge`, and keeps
puncture balance in its compiled-target encoded form while its graph-level
form remains in the independent `lean_search_tree` development. The later
compatibility revisions completed both external Lean builds; see
`EXTERNAL_VERIFICATION_RECORD.md`.
