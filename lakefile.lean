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
    @ "483848e8afb952d25f51f5ab865b4b3525c086b9"

require verso from git
  "https://github.com/leanprover/verso"
    @ "1428bd0ee7dd76f63315aaa77953aac5adcc4c0b"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "5fcaebf576d110067601099234a110a8ee2a9173"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "1507142f79f05371e5eb25202eec6396bb940d72"

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
