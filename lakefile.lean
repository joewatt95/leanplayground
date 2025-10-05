import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "bd3b236511d9a8929791f20f775e98a9ef81697c"

require "ufmg-smite" / smt @
  git "d6c048b99c80e93c42e7fb03ba5b14a74b00a836"

require "chasenorman" / Canonical @
  git "v4.23.0"

require "JOSHCLUNE" / Hammer @
  git "v4.23.0"

require "marcusrossel" / egg @
  git "13abfc8437528eeb0088ef223e778c94b069dac7"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "15beac7f2a5913571cba016e4b87fed907c54f7d"

require "leanprover" / verso @
  git "v4.23.0"

require "leanprover-community" / mathlib @
  git "v4.23.0"
