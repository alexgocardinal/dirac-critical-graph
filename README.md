# An explicit order-60 solution of Dirac's k=4 critical-graph problem

This repository accompanies the paper and supplies the explicit graph,
two complementary Lean 4 certificates, independent verification programs,
and reproducibility records.

**Accompanying paper:** *Allocating Divested Assets under Antitrust Regulation: A Graph-Theoretic Obstruction and the Resolution of Dirac’s Conjecture* (previously *Topological Limits of Behavioral Regulation in
Antitrust*), Alex Chan (Harvard University and NBER),
[ORCID 0000-0002-2116-4544](https://orcid.org/0000-0002-2116-4544).

## Main result

There is an explicit finite graph `G` on 60 vertices such that:

- `chi(G) = 4`;
- `chi(G - v) = 3` for every vertex `v`;
- `chi(G - e) = 4` for every edge `e`.

Thus `G` is 4-vertex-critical and has no critical edges. The final structured
Lean statement is:

```lean
Dirac60.order60_solution :
  FourVertexCritical G ∧ EdgeImmuneAtFour G
```

Both Lean projects built successfully with Lean 4.19.0 and Mathlib v4.19.0.
Their final axiom reports contain no `sorryAx`. Concrete finite checks use
`native_decide`, so the reported trust boundary includes `Lean.ofReduceBool`.
See [verification/EXTERNAL_VERIFICATION_RECORD.md](verification/EXTERNAL_VERIFICATION_RECORD.md).

## Explicit graph

Let `Gamma = Z/12Z x Z/5Z` with multiplication

```text
(e,i)(f,j) = (e+f mod 12, i + 2^e j mod 5)
```

and let

```text
S = {(1,0),(11,0),(5,1),(7,2),(6,0),(6,3)}.
```

The graph is the undirected Cayley graph `Cay(Gamma,S)`, using vertex label
`5e+i`. It is simple, connected, vertex-transitive, 6-regular, and has 180
edges. Its frozen edge-list digest is:

```text
85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c
```

## Verification routes

| Route | What it checks | Final outcome |
| --- | --- | --- |
| `lean_bv/` | Fully unrolled Boolean/SAT certificate, all vertex-deletion witnesses, proper 4-colouring, and `q3(G) >= 2` | Build and executable passed |
| `lean_search_tree/` | Generic checker soundness, 21 explicit search trees, balanced-puncture transport, and final graph theorem | Build, axiom audit, 35,967-node replay, and checksums passed |
| `verifier/` and `audits/` | Independent structural and exact finite checks | Passed |

## Reproduce the compact Lean certificate

Install [elan](https://github.com/leanprover/elan), then run:

```sh
cd lean_bv
lake update
lake exe cache get
lake build
lake exe dirac60-check
```

Expected final output includes:

```text
Dirac60 Lean certificate elaborated successfully.
edges: 180
all concrete vertex witnesses valid: true
displayed three-colour defect: 2
```

## Reproduce the independent structured certificate

```sh
cd lean_search_tree
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
python3 replay_certificates.py
sha256sum --check SHA256SUMS
```

On macOS, replace the last command with:

```sh
shasum -a 256 -c SHA256SUMS
```

The replay should report `PASS cases=21 nodes=35967`.

## Repository map

- `paper/` - PDF report, LaTeX manuscript, and plain-text result.
- `graph/` - canonical edge list, graph6 encoding, witness, and construction manifest.
- `lean_bv/` - compact Boolean/SAT Lean development.
- `lean_search_tree/` - independent structured Lean development.
- `verifier/` - standalone Python and C++ verifiers.
- `audits/` - static and independent certificate audits.
- `verification/` - external build record and instructions for preserving logs.
- `docs/CLAIM_SCOPE.md` - exact mathematical and formal claim boundary.
- `generate_manifest.py` - regenerates the repository-wide SHA-256 manifest.

## Universal Decoupling Theorem: exact scope

For `k >= 2`, let `D(k)` mean that there exists a finite simple graph `H`
with `chi(H)=k`, every vertex deletion having chromatic number `k-1`, and every
single-edge deletion retaining chromatic number `k`. Mathematically,

```text
D(k) if and only if k >= 4.
```

The order-60 graph supplies the Lean-checked `k=4` case. The `k>=5` direction
uses Jensen's published theorem. `UniversalDecoupling.iff_ge_four` formalizes
the final logical deduction with Jensen's result retained as an explicit
hypothesis; this repository does not formalize Jensen's infinite family.

This theorem is existential by chromatic level. It does **not** say that every
vertex-critical graph of chromatic number at least four is edge-immune; `K4`
is a counterexample to that pointwise reading.

## Citation, license, and status

Citation metadata is provided in `CITATION.cff`. This repository is released
under the MIT License; see `LICENSE`. Follow `PREPUBLICATION_CHECKLIST.md`
before publishing.

The formal and computational checks reported here have passed. Independent
public reproduction, expert inspection, and peer review remain necessary
before treating the result as accepted in the mathematical literature.
