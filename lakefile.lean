import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "PatrickMassot" / verbose @ git "a2f87b133d5b5e1b0b81d4fd7586b8750c08c5db"

require "chasenorman" / Canonical @ git "65e13dfb3d308177f560ea3347dd7fc94749076e"

require "JOSHCLUNE" / Hammer @ git "v4.32.0"

require sos from git
  "https://github.com/leanprover/sos" @ "cfc0ab897c3ecdbd6779aa3d6bce9ac5b3c76199"

require "nomeata" / calcify @ git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @ git "9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0"

require "leanprover" / verso @ git "v4.32.0"

require "leanprover-community" / mathlib @ git "v4.32.2"
