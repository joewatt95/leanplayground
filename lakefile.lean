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
    @ "e660590af7007c123412ccb229a3f29b8620bd15"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "7efc519da69167122d5a8797b47ca11661fbe98c"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "c2a2c0a08d7cabd66b4cc2dc2ce2b77b26be2c95"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "1df4ebfd04ea5bfe44b27bcd322dd0d8a2d89ac5"

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
