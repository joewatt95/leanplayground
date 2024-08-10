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
    @ "ea3e51bd2452f760c97e55c887a716899d4d19e5"

require leanses from git
  "https://github.com/VCA-EPFL/leanses"
    @ "95bc5ddd93553ae416ced18839cccbcff6b2a01c"

require verso from git
  "https://github.com/leanprover/verso"
    @ "000647872db8486c7f520f3c411134a8a9c9868e"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "5a1a7518ad98cafd27eaa17fcaadd61dc183e9d2"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
