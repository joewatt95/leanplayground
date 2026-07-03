import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "v4.30.0"

-- require "ufmg-smite" / smt @
--   git "7d1d8239e78daa5197f9a71948776c4627049f5f"

require "chasenorman" / Canonical @ git "v4.30.0"

require "JOSHCLUNE" / Hammer @ git "v4.30.0"

require sos from
  git "https://github.com/leanprover/sos" @
  "d4975cad5b98688121ba1ef17693e126b6d5f7f7"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "e668239956d4d85547e1f6393fbf923a2d47ade7"

require "leanprover" / verso @ git "v4.30.0"

require "leanprover-community" / mathlib @ git "v4.30.0"
