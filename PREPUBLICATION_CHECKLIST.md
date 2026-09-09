# Pre-publication checklist

Complete every unchecked item before making the repository public.

## Identity and paper metadata

- [x] Identify the single author as Alex Chan, Harvard University and NBER.
- [x] Set the final paper title everywhere.
- [x] Add ORCID 0000-0002-2116-4544.
- [ ] Add the arXiv identifier and DOI when available.
- [x] Complete `CITATION.cff`.

## Legal choices

- [x] Select the MIT License for the repository.
- [x] Add the MIT license file and remove the license-selection placeholder.
- [x] The single author selected the license.

## Verification evidence

- [x] Copy `lean_bv/lake-manifest.json` from the successfully built compact
      project.
- [ ] Copy `lean_search_tree/lake-manifest.json` from the successfully built
      structured project, if Lake generated it.
- [x] Copy the original compact Lean build log into `verification/logs/`.
- [x] Copy `Dirac60_structured_axioms.txt` into `verification/logs/`.
- [x] Copy `Dirac60_search_tree_replay.txt` into `verification/logs/`.
- [x] Copy `Dirac60_structured_hash_check.txt` into `verification/logs/`.
- [ ] If available, add a structured `lake build` transcript.
- [x] Run the root `MANIFEST.sha256` check after adding final logs.
- [x] Run `python3 generate_manifest.py` after every final tracked-file change.
- [x] Run `shasum -a 256 -c MANIFEST.sha256` and confirm every entry is `OK`.

## Claim discipline

- [x] Keep the `Lean.ofReduceBool` trust disclosure.
- [x] State that the universal Lean theorem is conditional on Jensen's input.
- [x] Do not call Jensen's infinite family formalized unless it is later added.
- [x] Keep the statement existential by chromatic number.
- [x] Do not claim peer-reviewed acceptance before peer review occurs.

## GitHub release

- [ ] Confirm `.github/workflows/verify.yml` passes on GitHub Actions.
- [ ] Inspect `git status` for secrets and build products.
- [ ] Tag the checked commit as `v1.0.0`.
- [ ] Publish the release notes and paper PDF.
- [ ] Archive the release with Zenodo or another repository if a DOI is wanted.
