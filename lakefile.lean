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
    @ "7bf250a5056a0a58937287046d06dcc2d8e1c94a"

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
    @ "f46663afcd4067a606094dda363f67922e6990a4"

require sampcert from git
  "https://github.com/leanprover/SampCert"
    @ "a71f5dbdc797bec25118830b976fc75f2e178a24"

require leanses from git
  "https://github.com/VCA-EPFL/leanses"
    @ "6c99a8cfb3315f13cfcf55acf1b633fba45bc3dd"

require verso from git
  "https://github.com/leanprover/verso"
    @ "06b60f9723aadb9cabf2631b90ea721d1c6ef2dd"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "7241c81793e4f1439a50775bcf5e418fac7ee88d"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
