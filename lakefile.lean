import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "c9e42865f7fd26d5f03bb91cc47cff057e88e294"

-- require "ufmg-smite" / smt @ git
--   "3bc19f2d3caba4c5fbfe213143c79364c3d9c97a"

require "chasenorman" / Canonical @ git "v4.28.0-rc1"

require "JOSHCLUNE" / Hammer @ git "v4.28.0"

require "Joewatt95" / egg from git
  "https://github.com/Joewatt95/lean-egg" @
  "8b978c7e1614dc88b1165d0543141412f8631e29"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "36960b00cfb2636927c22f9e3c2cadfde78e70e5"

require "leanprover" / verso @ git "v4.28.0"

require "leanprover-community" / mathlib @ git "v4.28.0"
