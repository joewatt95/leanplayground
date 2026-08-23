import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

require "chasenorman" / Canonical @ git "65e13dfb3d308177f560ea3347dd7fc94749076e"

require "JOSHCLUNE" / Hammer @ git "f6d189d1d7cfb34d28d447c1a67a118539ab44f4"

require "leanprover"/ sos @ git "cfc0ab897c3ecdbd6779aa3d6bce9ac5b3c76199"
require CSDP from git "https://github.com/leanprover/csdp-ffi" @ "v0.1.2"
require HexMvPolyMathlib from git
  "https://github.com/leanprover/hex-mv-poly-mathlib" @
  "7f84a99d59cc71b968f1a4040dfb40cdd9f32042"

require "nomeata" / loogle @ git "9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0"

require "PatrickMassot" / verbose @ git "a2f87b133d5b5e1b0b81d4fd7586b8750c08c5db"

require "leanprover" / verso @ git "v4.33.0"

require "leanprover-community" / mathlib @ git "v4.33.1"
