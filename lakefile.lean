import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @
  git "v4.31.0"

-- require "ufmg-smite" / smt @
--   git "7d1d8239e78daa5197f9a71948776c4627049f5f"

require "chasenorman" / Canonical @ git "65e13dfb3d308177f560ea3347dd7fc94749076e"

require "JOSHCLUNE" / Hammer @ git "c9ea5bf1b61bbfbf2dc48c08d3f8c0ee43362153"

-- require sos from
--   git "https://github.com/leanprover/sos" @
--   "d4975cad5b98688121ba1ef17693e126b6d5f7f7"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0"

require "leanprover" / verso @ git "v4.32.0"

require "leanprover-community" / mathlib @ git "v4.32.0"
