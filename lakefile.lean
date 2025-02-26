import Lake
open Lake DSL

-- This is needed because we compile and link against the C++ API of cvc5.
-- private def args : Array String :=
--   #[s!"--load-dynlib={libcpp}"]
--   where
--     libcpp :=
--       if System.Platform.isWindows then "libstdc++-6.dll"
--       else if System.Platform.isOSX then "libc++.dylib"
--       else "libstdc++.so.6"

package leanplayground where
  -- moreLeanArgs := args
  -- moreGlobalServerArgs := args

  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "7241c81793e4f1439a50775bcf5e418fac7ee88d"

-- require "ufmg-smite" / smt @
--   git "7b8651b39629159540430f83208fd812c6e8a0bc"

require "leanprover-community" / Duper @
  git "v0.0.23"

require "marcusrossel" / egg @
  git "6b3f40f82666b1ec6b2ea2868e8948353a075143"

require "nomeata" / loogle @
  git "d56dbe9a1637c1160862deb9da8d621682e46013"

require "leanprover" / verso @
  git "v4.16.0"

require "leanprover-community" / mathlib @
  git "v4.16.0"
