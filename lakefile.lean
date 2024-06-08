import Lake
open Lake DSL

private def libcpp : String :=
  if System.Platform.isWindows then "libstdc++-6.dll"
  else if System.Platform.isOSX then "libc++.dylib"
  else "libstdc++.so.6"

private def args : Array String := #[s!"--load-dynlib={libcpp}"]

package leanplayground where
  precompileModules := true
  moreLeanArgs := args
  moreGlobalServerArgs := args
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

@[default_target]
lean_lib Leanplayground where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
    @ "v4.8.0"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.12"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "6cffc706e5f0824a7696137c3675f984323ef9e4"

require smt from git
  "https://github.com/joewatt95/lean-smt"
    @ "56b72670e0fbf703132db7aa98fbc6499a8b6241"
  -- "https://github.com/ufmg-smite/lean-smt"
  --   @ "64d482b74c32913120a7e6de9145e92433532200"

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
