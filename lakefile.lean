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
  git "bd3b236511d9a8929791f20f775e98a9ef81697c"

-- require "ufmg-smite" / smt @
--   git "db6a7caf8685b33897ceebc9159bb1e180e2c568"

-- require "leanprover-community" / Duper @
--   git "v0.0.26"

require "chasenorman" / Canonical @
  git "v4.21.0"

require "JOSHCLUNE" / Hammer @
  git "v4.21.0"

require "marcusrossel" / egg @
  git "136ed2d95601d4b84fda05fb7afb85ebbf36492b"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "ff045300e699fe9e890d098b302985eb9b191410"

require "leanprover" / verso @
  git "v4.21.0"

require "leanprover-community" / mathlib @
  git "v4.21.0"
