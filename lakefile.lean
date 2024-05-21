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
    @ "f3ca78288e785e4c4219ab0e6a88af33dcb5b85f"

require verso from git
  "https://github.com/leanprover/verso"
    @ "259608efe53b1aeb02a44f2d4ce68bdfdac85956"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "0fef059edf6bf2da0fcdf03100ca6631fb73d79a"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "664c8f272a9f5552fd1bac68644e0d3b19c9438e"

-- require egg from git
--   "https://github.com/marcusrossel/lean-egg"
--     @ "1df4ebfd04ea5bfe44b27bcd322dd0d8a2d89ac5"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.11"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "34713b27a0cab653313288397c5f0efb6b2061b0"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
