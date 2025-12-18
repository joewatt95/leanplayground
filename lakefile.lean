import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "c978de71e0241a2cf7e6010e562ead8d508115ef"

-- require "Joewatt95" / smt from git
--   "https://github.com/Joewatt95/lean-smt" @
--   "e8a675569cd2fcd4b916ff173aff8a17d7682718"

require "chasenorman" / Canonical @ git "v4.26.0"

require "JOSHCLUNE" / Hammer @ git "v4.26.0"

require "Joewatt95" / egg from git
  "https://github.com/Joewatt95/lean-egg" @
  "cff704447cfdb85126d16557a9ec050b27e33b64"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "0ac13cd97d030b989151359429f9061c12faf0f6"

require "leanprover" / verso @ git "v4.26.0"

require "leanprover-community" / mathlib @ git "v4.26.0"
