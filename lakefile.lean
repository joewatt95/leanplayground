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
    @ "609dbd06021977f202806f01a0bb08b28e912406"

require verso from git
  "https://github.com/leanprover/verso"
    @ "74a3b2707d6d6e00ae0dc99a99b98b220aa0eaab"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "b356076812e7be32baa89b8bc85f83a00d0f9776"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "218dbe258c93ec0431d6a71106bfca11642b415c"

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
