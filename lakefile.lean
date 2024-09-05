import Lake
open Lake DSL

-- This is needed because we compile and link against the C++ API of cvc5.
private def args : Array String :=
  #[s!"--load-dynlib={libcpp}"]
  where
    libcpp :=
      if System.Platform.isWindows then "libstdc++-6.dll"
      else if System.Platform.isOSX then "libc++.dylib"
      else "libstdc++.so.6"

package leanplayground where
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
    @ "v4.9.1"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "f4c5e9b93b08a7a1097e04c798645146727fffcf"

require smt from git
  "https://github.com/ufmg-smite/lean-smt"
    @ "b332ae49450b88c5ead40d66e4d786cb5d991ea9"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "abaab85d51d33ef01ed8c757bfb49cc55abae229"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot"
--     @ "v1.4.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "7eaed1d5ef13b7c81d71fa1f0116c93c83cc0b0c"

require sampcert from git
  "https://github.com/leanprover/SampCert"
    @ "a71f5dbdc797bec25118830b976fc75f2e178a24"

require leanses from git
  "https://github.com/VCA-EPFL/leanses"
    @ "d2e0a39bd05b0c49d9211c2b0dd5d5c62c701fe0"

require verso from git
  "https://github.com/leanprover/verso"
    @ "211324b7781e85202bf885f6accac506ca9de5e9"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "5a1a7518ad98cafd27eaa17fcaadd61dc183e9d2"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
