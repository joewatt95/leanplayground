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
  git "a3331b46c2909064d247367f321c14815c34eead"

-- require "ufmg-smite" / smt @
--   git "db6a7caf8685b33897ceebc9159bb1e180e2c568"

-- require "leanprover-community" / Duper @
--   git "v0.0.26"

require "chasenorman" / Canonical @
  git "v4.21.0"

require "JOSHCLUNE" / Hammer @
  git "v4.21.0"

require "marcusrossel" / egg @
  git "06a9373cd5a8cb1c20bbd4b8bf41d416b956b6cd"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "2c2d6a298b46081fb751f971677e702d460160d4"

require "leanprover" / verso @
  git "v4.21.0"

require "leanprover-community" / mathlib @
  git "v4.21.0"
