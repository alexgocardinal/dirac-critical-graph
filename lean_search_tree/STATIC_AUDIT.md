# Static audit report

Date: 2026-09-09

## Completed checks

- No `sorry`, `admit`, `unsafe`, or user `axiom` declarations occur in the
  Lean sources.
- `replay_certificates.py` independently accepted all 21 certificate trees,
  all 35,967 nodes, and rejected absent/spurious child branches by design.
- The edge list has 180 distinct edges, every endpoint is in `Fin 60`, and
  every vertex has degree six during both generation and replay.
- The certificate forest regenerates deterministically from the frozen edge
  list.
- Static review checked the semantic chain:
  `Valid` -> no list-colouring -> no missing/unique neighbour colour ->
  two of every colour at the root -> Cayley transport -> exact 2+2+2 at every
  puncture -> 4-vertex-critical and edge-immune.
- `sha256sum --check SHA256SUMS` passes.

## Frozen identities

- Edge list SHA-256:
  `85914250312a4fe8d1a67d747fea2ee1772c9762796af90095efa61fb4c0400c`
- JSON certificate SHA-256:
  `5959d3f0943bba98e2278ae567f7bbe2a406e41f7ce2015fa6e0101b9449e195`

## Unresolved release check

No Lean executable was installed in this workspace and downloading a
toolchain was unavailable during this static audit. The modules subsequently
completed an external Lean 4.19.0 build; see
`../EXTERNAL_VERIFICATION_RECORD.md`.
Possible remaining failures are elaboration/API mismatches rather than known
logical gaps; the highest-risk sites are the large generated term,
`fin_cases`, and finite-set cardinality lemma names in the exact-profile
proof. Run `lake build` under the pinned toolchain before claiming successful
Lean compilation.

All concrete finite facts and tree validations use `native_decide`. Even after
successful compilation, the final theorem is not kernel-reduction-only: it
inherits Lean's native-decision result axiom/code-generator trust boundary.
Run `lake env lean AxiomAudit.lean` and preserve its output with any release.
