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
    @ "v0.0.15"

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
    @ "e0447ffabecf5ff3eff6b2cea6a81346abadbec1"

require leanses from git
  "https://github.com/VCA-EPFL/leanses"
    @ "95bc5ddd93553ae416ced18839cccbcff6b2a01c"

require verso from git
  "https://github.com/leanprover/verso"
    @ "e223cfcc12428144130fd2b20e5801675d29de6b"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "5a1a7518ad98cafd27eaa17fcaadd61dc183e9d2"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
