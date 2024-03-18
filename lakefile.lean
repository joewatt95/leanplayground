import Lake
open Lake DSL

package leanplayground where
  -- add any package configuration options here
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

@[default_target]
lean_lib Leanplayground where
  -- add any library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.6.1"

require verso from git
  "https://github.com/leanprover/verso"
    @ "3e44cd7cb8b2e757a4aa57c3a6f5a51e058c3db0"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot" @ "v1.1.2"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "312b53abc724fe1eed2f1f9f4e570b30a59b501d"

require auto from git
  "https://github.com/leanprover-community/lean-auto" @ "v0.0.7"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.6"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "f1f010fe08ba2b83cf68215e0aac94807de69460"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
