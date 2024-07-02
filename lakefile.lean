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
    @ "v4.8.0"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "v0.0.14"

require smt from git
  "https://github.com/ufmg-smite/lean-smt"
    @ "2899f02744cc12636f71c04e200bce0b308f73b5"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "abaab85d51d33ef01ed8c757bfb49cc55abae229"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot"
--     @ "v1.3.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "cd8680514b046e71b79183bf3c64de3350cd0c10"

require verso from git
  "https://github.com/leanprover/verso"
    @ "0bb0440f81f28507ce6d142d5ff68a0623d9a69d"

require verbose from git
  "https://github.com/PatrickMassot/verbose-lean4"
    @ "213cffdee33ad52a134e40964ef88cef35314162"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
