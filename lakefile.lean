import Lake
open Lake DSL

package leanplayground where
  -- add any package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.0.2"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "main"

require Duper from git
  "https://github.com/leanprover-community/duper.git" @ "v0.0.5"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"

@[default_target]
lean_lib Leanplayground where
  -- add any library configuration options here
