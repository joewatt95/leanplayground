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
    @ "c641f2b9cd5aee7aa641d368f6604d077eb4cd54"

require verso from git
  "https://github.com/leanprover/verso"
    @ "a2945308a57483b75d13913e39b3fca662efd5bc"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "b356076812e7be32baa89b8bc85f83a00d0f9776"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "e2fe232c8ddb82a654842b8f05a588f33b1c7ca1"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "2a92f810e3c0c3f9431c6abc1588f540ca621f49"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "34713b27a0cab653313288397c5f0efb6b2061b0"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
