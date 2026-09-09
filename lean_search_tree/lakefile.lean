import Lake
open Lake DSL

package «dirac60-formal» where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib Dirac60Formal where
  roots := #[`BalancedPuncture, `Dirac60, `Dirac60Certificates,
    `Dirac60Result, `UniversalDecoupling, `AxiomAudit]
