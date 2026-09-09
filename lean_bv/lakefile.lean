import Lake
open Lake DSL

package «dirac60-certificate» where
  version := v!"1.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

lean_lib Dirac60

@[default_target]
lean_exe «dirac60-check» where
  root := `Main
