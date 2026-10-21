import Lake
open Lake DSL

package leanplayground where

@[default_target]
lean_lib Leanplayground where

lean_lib «LeanplaygroundUtil» where
  globs := #[.andSubmodules `TLogs.Util]

require "chasenorman" / Canonical @ git "v4.34.0"

require "JOSHCLUNE" / Hammer @ git "v4.34.0"

require "leanprover" / sos @ git "v0.2.4"

require "nomeata" / loogle @ git "9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0"

require "PatrickMassot" / verbose @ git "a2f87b133d5b5e1b0b81d4fd7586b8750c08c5db"

require "leanprover" / verso @ git "v4.34.0"

require "leanprover-community" / mathlib @ git "v4.34.1"
