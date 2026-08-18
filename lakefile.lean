import Lake
open Lake DSL

package MorganTianCh01 where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

@[default_target]
lean_lib MorganTianLib where
  roots := #[`MorganTianLib]
  globs := #[.andSubmodules `MorganTianLib]
