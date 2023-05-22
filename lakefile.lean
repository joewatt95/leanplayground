import Lake
open Lake DSL

package «leanplayground» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git"@"main"

@[default_target]
lean_lib «Leanplayground» {
  -- add any library configuration options here
}
