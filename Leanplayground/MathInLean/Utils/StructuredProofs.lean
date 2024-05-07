import Lean

namespace StructuredProofs

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax


@[term_parser] def «fix» :=
  leading_parser withPosition ("fix " >> many1 Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

@[term_parser] def «assume» :=
  leading_parser withPosition ("assume " >> Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

macro_rules
| `(fix $x* : $ty; $y) => `(λ $x* : $ty ↦ $y)
| `(assume $h : $ty; $y) => `(λ $h : $ty ↦ $y)

end StructuredProofs
