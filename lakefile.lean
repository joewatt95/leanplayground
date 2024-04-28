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
    @ "0b522a14d05af74adeb78e7e2853fe288d53d507"

require verso from git
  "https://github.com/leanprover/verso"
    @ "82e23329cf7088f5b39dd1c61e243ba6350e5055"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "7efc519da69167122d5a8797b47ca11661fbe98c"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "12e31756e3e97f167493e251165d77569b01c504"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "98cc99fc30243e2a73c0044377479c1a46ff56a4"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "34713b27a0cab653313288397c5f0efb6b2061b0"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt.git" @ "main"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
