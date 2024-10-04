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

require "leanprover-community" / "mathlib"
  @ "git#v4.11.0"

require "leanprover-community" / "Duper"
  @ "git#v0.0.16"

require "ufmg-smite" / "smt"
  @ "git#0b418049bf228d55c782223ce6fa53148b77cc79"

require "marcusrossel" / "egg"
  @ "git#c51f43f79a4ed5dacadc7ae2500828b6534bfab3"

-- require "LeanCopilot"
--   @ "git#v1.4.0"

require "nomeata" / "loogle"
  @ "git#f46663afcd4067a606094dda363f67922e6990a4"

require "leanprover" / "sampcert"
  @ "git#9cb42e1befdf5968b61cda66355607e5571a4039"

-- require "leanses"

require "leanprover" / "verso"
  @ "git#33b0ed5626cf5494a96d3a51efe376bdadf9cf63"

require "PatrickMassot" / "verbose"
  @ "git#7241c81793e4f1439a50775bcf5e418fac7ee88d"

-- require LeanCodePrompts from git
--   "https://github.com/siddhartha-gadgil/LeanAide" @ "main"
