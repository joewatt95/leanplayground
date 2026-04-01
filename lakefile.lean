import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "3bb939135f3b46f6028408442644766ed9d5ec55"

-- require "ufmg-smite" / smt @ git
--   "3bc19f2d3caba4c5fbfe213143c79364c3d9c97a"

require "chasenorman" / Canonical @ git "v4.29.0"

require "JOSHCLUNE" / Hammer @ git "v4.29.0"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "8e80836a86196849b2393e7a752d6100c17b772d"

require "leanprover" / verso @ git "v4.29.0"

require "leanprover-community" / mathlib @ git "v4.29.0"
