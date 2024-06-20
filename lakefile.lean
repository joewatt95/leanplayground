import Lake
open Lake DSL

-- private def libcpp : String :=
--   if System.Platform.isWindows then "libstdc++-6.dll"
--   else if System.Platform.isOSX then "libc++.dylib"
--   else "libstdc++.so.6"

-- private def args : Array String := #[s!"--load-dynlib={libcpp}"]

package leanplayground where
  -- precompileModules := true
  -- moreLeanArgs := args
  -- moreGlobalServerArgs := args
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

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt"
--     @ "1c870041542025ee49184112b8ca372adb9b7ecd"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.2"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "5faf10c5a55c01b1b55585fe44311414df5af3c4"

require verso from git
  "https://github.com/leanprover/verso"
    @ "b51349a1af0e0429e5e30343e6e6127b01db5911"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "0fef059edf6bf2da0fcdf03100ca6631fb73d79a"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
