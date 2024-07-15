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
    @ "d53f474c91d39d49d0d30fa8d8deca51c4559690"

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
    @ "fcc2c2c7ef12039d774a89f4bfb59483243f45b6"

require verso from git
  "https://github.com/leanprover/verso"
    @ "2b9840397386e431b127cb04212b5ed04e010015"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "213cffdee33ad52a134e40964ef88cef35314162"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
