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
  "https://github.com/leanprover-community/mathlib4"
    @ "v4.8.0"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.12"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "6cffc706e5f0824a7696137c3675f984323ef9e4"

require cvc5 from git
  "https://github.com/anzenlang/lean-cvc5"
    @ "5c18f7fe381143b62ef9d809b52214405cdc7c9e"

require smt from git
  "https://github.com/ufmg-smite/lean-smt"
    @ "95747e9bf4bda4f80a7bf359cf774b8514633328"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.2"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "387ab85308ce817bb95cc99730025eb44cb8a9ab"

require verso from git
  "https://github.com/leanprover/verso"
    @ "297444dc7fc47066872156c58220bcc21c0b2aab"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "0fef059edf6bf2da0fcdf03100ca6631fb73d79a"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
