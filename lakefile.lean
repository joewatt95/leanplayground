import Lake
open Lake DSL

package leanplayground where
  -- add any package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

@[default_target]
lean_lib Leanplayground where
  -- add any library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
    @ "a36350f2089912de4d11fbccb92d7575bf9f28e0"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.1.1"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"

require auto from git
  "https://github.com/leanprover-community/lean-auto" @ "v0.0.7"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.6"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "c6903e48f1441118b6d27489d884eb0893278e2f"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
