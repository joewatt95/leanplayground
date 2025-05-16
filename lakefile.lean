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
--   git "da4ba9acf1845fe264b2bce14923f8e09fbabf28"

require "leanprover-community" / Duper @
  git "v0.0.26"

require "chasenorman" / Canonical @
  git "v4.20.0-rc3"

require "marcusrossel" / egg @
  git "0d83adaa4606f04bba8090105cc577fb70d6647a"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "19971e9e513c648628fc733844b818d6816534c5"

require "leanprover" / verso @
  git "v4.20.0-rc2"

require "leanprover-community" / mathlib @
  git "v4.20.0-rc5"
