# v1.0.0 - Order-60 certificate release

Companion repository for *Topological Limits of Behavioral Regulation in
Antitrust* by Alex Chan (Harvard University and NBER), ORCID
0000-0002-2116-4544.

Initial public artifact release accompanying the paper.

## Included

- explicit 60-vertex, 180-edge Cayley graph;
- compact Lean Boolean/SAT certificate;
- independent Lean search-tree certificate with 35,967 nodes;
- generic balanced-puncture theorem and soundness proof;
- displayed vertex-deletion and 4-colouring witnesses;
- independent Python and C++ verification programs;
- corrected SHA-256 manifests;
- PDF, LaTeX, and plain-text paper materials;
- exact claim-scope and trust-boundary documentation.

## Verified results

- both Lean 4.19.0 / Mathlib v4.19.0 projects build successfully;
- final theorem axiom reports contain no `sorryAx`;
- all 21 search-tree cases and all 35,967 nodes replay successfully;
- edge digest:
  `85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c`;
- certificate digest:
  `5959d3f0943bba98e2278ae567f7bbe2a406e41f7ce2015fa6e0101b9449e195`.

## Trust and scope

Concrete finite checking uses Lean's native evaluation path and reports
`Lean.ofReduceBool`. The all-chromatic-level corollary additionally uses
Jensen's published `k>=5` theorem; that infinite family is not formalized in
this release.
