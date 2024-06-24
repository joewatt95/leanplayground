import Lake
open Lake DSL

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
    @ "v4.8.0"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "8077ac787b604ff16a854931058ec4c788932c6f"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "abaab85d51d33ef01ed8c757bfb49cc55abae229"

require smt from git
  "https://github.com/ufmg-smite/lean-smt"
    @ "2899f02744cc12636f71c04e200bce0b308f73b5"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot"
--     @ "v1.3.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "5faf10c5a55c01b1b55585fe44311414df5af3c4"

require verso from git
  "https://github.com/leanprover/verso"
    @ "e157703f8c898d3ba3ad701a6d9141c7e4c8742c"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "0fef059edf6bf2da0fcdf03100ca6631fb73d79a"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
