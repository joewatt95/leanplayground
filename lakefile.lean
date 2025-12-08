import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "c978de71e0241a2cf7e6010e562ead8d508115ef"

require "Joewatt95" / smt from git
  "https://github.com/Joewatt95/lean-smt" @
  "8dd8570482e02fd780a5e935d174677820f08d1e"

require "chasenorman" / Canonical @ git "v4.25.0"

require "JOSHCLUNE" / Hammer @ git "v4.25.2"

require "Joewatt95" / egg from git
  "https://github.com/Joewatt95/lean-egg" @
  "1f3caba4d7504adb747215ad981be979410762be"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "0ac13cd97d030b989151359429f9061c12faf0f6"

require "leanprover" / verso @ git "v4.25.1"

require "leanprover-community" / mathlib @ git "v4.25.2"
