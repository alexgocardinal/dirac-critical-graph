# Reproducibility guide

## Pinned environment

- Lean: 4.19.0
- Mathlib: v4.19.0
- Graph order: 60
- Graph size: 180
- Edge digest: `85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c`
- Search-tree data digest: `5959d3f0943bba98e2278ae567f7bbe2a406e41f7ce2015fa6e0101b9449e195`

Each Lean project contains its own `lean-toolchain` and `lakefile.lean`.

## One-command overview

From the repository root on macOS or Linux:

```sh
python3 verifier/verify_structure.py
python3 audits/independent_certificate_audit.py
```

Then build each Lean project using the commands below.

## Compact certificate

```sh
cd lean_bv
lake update
lake exe cache get
lake build
lake exe dirac60-check
python3 audit_generation.py
cd ..
```

The final compact theorem is `Dirac60.certified_dirac_result`.

## Independent structured certificate

```sh
cd lean_search_tree
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
python3 replay_certificates.py
```

Linux integrity check:

```sh
sha256sum --check SHA256SUMS
```

macOS integrity check:

```sh
shasum -a 256 -c SHA256SUMS
```

The final structured theorem is `Dirac60.order60_solution`.

## Standalone C++ verifier

```sh
g++ -std=c++20 -O3 verifier/verify_candidate60.cpp -o verify_candidate60
./verify_candidate60 graph/candidate60.edgelist
```

The generated binary is intentionally excluded from Git.

## Root manifest

Regenerate it after adding metadata, licenses, logs, or Lake manifests:

```sh
python3 generate_manifest.py
```

Linux:

```sh
sha256sum --check MANIFEST.sha256
```

macOS:

```sh
shasum -a 256 -c MANIFEST.sha256
```

The manifest identifies repository bytes; it does not replace Lean checking.

## Trust boundary

The abstract checker-soundness and balanced-puncture arguments are ordinary
Lean proof terms. Concrete finite graph facts and certificate validation use
`native_decide`, whose reported axiom footprint includes `Lean.ofReduceBool`.
The compact negative certificate uses `bv_decide` and reports the same final
footprint after composition with concrete witness checks.

The universal logical-glue theorem takes Jensen's `k>=5` result as an explicit
hypothesis. This repository does not formalize Jensen's published construction.
