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

require "PatrickMassot" / verbose @
  git "7241c81793e4f1439a50775bcf5e418fac7ee88d"

require "ufmg-smite" / smt @
  git "9ad1c39d47fe3a8af885b5c0168afda11ed8c021"

require "leanprover-community" / Duper @
  git "15bd942bfd58cc85cbce782cb80f86f1110acc61"

require "marcusrossel" / egg @
  git "3c1a713c803c08cb8be8f6adc89394441eb7fbb0"

require "nomeata" / loogle @
  git "4e1aab07fa10f263a2110787180f8f5db93ee650"

require "leanprover" / verso @
  git "v4.14.0"

require "leanprover-community" / mathlib @
  git "dde4f2ecaec222a1c7db638d7536f0b195d8e953"
