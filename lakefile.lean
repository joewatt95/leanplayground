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

require "leanprover-community" / "mathlib" @
  git "v4.12.0"

require "leanprover-community" / "Duper" @
  git "a500ea7a5b9eca0ecaa7b4a229786a61b2707d30"

require "joewatt95" / "smt"
  from git "https://github.com/joewatt95/lean-smt"
  @ "36fd08166cc76a0d1193bbb56ad66a24a98e19fc"

require "marcusrossel" / "egg" @
  git "e08d72aefb8a352fcb0bca2148f5392c9edca5f4"

-- require "LeanCopilot" @
--   git "v1.4.0"

require "nomeata" / "loogle" @
  git "f46663afcd4067a606094dda363f67922e6990a4"

require "leanprover" / "sampcert" @
  git "9cb42e1befdf5968b61cda66355607e5571a4039"

-- require "leanses"

require "leanprover" / "verso" @
  git "v4.12.0"

require "PatrickMassot" / "verbose" @
  git "7241c81793e4f1439a50775bcf5e418fac7ee88d"
