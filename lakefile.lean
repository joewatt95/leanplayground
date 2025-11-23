import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "c978de71e0241a2cf7e6010e562ead8d508115ef"

require "Joewatt95" / smt from git
  "https://github.com/Joewatt95/lean-smt" @
  "ccb6bde98c6931a7d4e02c1fb13f2afb19909c80"

require "chasenorman" / Canonical @
  git "v4.25.0"

require "JOSHCLUNE" / Hammer @
  git "v4.25.0"

require "Joewatt95" / egg from git
  "https://github.com/Joewatt95/lean-egg" @
  "9bb889b31d2029a5729ff06ce80248485c34e493"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "0ac13cd97d030b989151359429f9061c12faf0f6"

require "leanprover" / verso @
  git "v4.25.1"

require "leanprover-community" / mathlib @
  git "v4.25.1"
