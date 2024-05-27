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
    @ "b0eb4bbc7ec80e6be10133c9be693245d3461d26"

require verso from git
  "https://github.com/leanprover/verso"
    @ "297444dc7fc47066872156c58220bcc21c0b2aab"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.2"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "0fef059edf6bf2da0fcdf03100ca6631fb73d79a"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "91cd0e81ec8bd16baa2c08e3d00a7f8e473477b4"

-- require egg from git
--   "https://github.com/marcusrossel/lean-egg"
--     @ "1df4ebfd04ea5bfe44b27bcd322dd0d8a2d89ac5"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.12"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "fa2ddf5771cc25b0d6e552ef63b51a68351e437f"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
