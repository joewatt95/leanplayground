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
  git "155efdb446fee2e714306be0e2eb9b5b670cb124"

-- require "ufmg-smite" / smt @
--   git "1df3f342c196f3f9db3ab2a8204995f8ff9754a5"

require "leanprover-community" / Duper @
  git "v0.0.25"

require "marcusrossel" / egg @
  git "6b3f40f82666b1ec6b2ea2868e8948353a075143"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "b340a5b73a68fd54d624ac1f9c025c11f638bb53"

require "leanprover" / verso @
  git "v4.18.0"

require "leanprover-community" / mathlib @
  git "v4.18.0"
