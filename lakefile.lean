import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "c978de71e0241a2cf7e6010e562ead8d508115ef"

require "ufmg-smite" / smt @
  git "a62ff46dd0a9d2505c74f3160ec67c3e6d5e8adc"

require "chasenorman" / Canonical @
  git "v4.24.0"

require "JOSHCLUNE" / Hammer @
  git "v4.24.0"

require "Joewatt95" / egg from git
  "https://github.com/Joewatt95/lean-egg" @
  "64fedc4717140ce88635a128f4c9c21cd3ef3701"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "ee8c0388917eb6b594f24e1865d5b83230229252"

require "leanprover" / verso @
  git "v4.24.0"

require "leanprover-community" / mathlib @
  git "v4.24.0"
