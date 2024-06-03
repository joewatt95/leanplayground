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
    @ "7aa5faafc8815ed358053e05f51f4aea8e47f4e2"

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

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.12"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "5715f55d754b32f57fa32bf3187ca270caccebb3"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "fa2ddf5771cc25b0d6e552ef63b51a68351e437f"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git"
--     @ "9dbfde40c19776fe64b4b3ba1554033a8d7382de"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
