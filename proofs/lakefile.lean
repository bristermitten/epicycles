import Lake
open Lake DSL

package epicycles where
  leanOptions := #[⟨`autoImplicit, false⟩]
  lintDriver := "batteries/runLinter"


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

require leaner from git "https://github.com/SrGaabriel/leaner.git" @ "main"

@[default_target]
lean_lib Epicycles where
  globs := #[.andSubmodules `Epicycles]
