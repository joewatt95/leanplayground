import Lean

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

import Auto.Tactic
import Duper
import Canonical
import Egg
-- import Smt
-- import Smt.Real
-- import Smt.Auto

import LeanSearchClient
import Loogle.Find

-- open Lean Auto in
-- def Auto.duperRaw (lemmas : Array Lemma) (_inhs : Array Lemma) : MetaM Expr := do
--   let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
--     λ ⟨⟨proof, ty, _⟩, _⟩ ↦ do
--       return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true)
--   Duper.runDuper lemmas.toList 0

-- attribute [rebind Auto.Native.solverFunc] Auto.duperRaw

macro "setup_auto" : command => `(
  set_option auto.smt true
  set_option auto.smt.solver.name "z3"

  set_option trace.auto.smt.printCommands true
  set_option trace.auto.smt.result true

  set_option auto.tptp true
  set_option auto.tptp.solver.name "zipperposition"
  set_option auto.tptp.zeport.path "/home/joe/dev/zipperposition/portfolio"

  set_option auto.native true)

syntax "setup_trivial" manyIndent(tactic) : command

macro_rules
  | `(setup_trivial $[$tacs:tactic]*) => open Lean in do
    let mut cmds : Array <| TSyntax `command := #[]

    for opt in [`linter.unreachableTactic, `linter.unusedTactic] do
      cmds := cmds.push <|
        ← opt |> mkIdent |> (`(set_option $(.) false))

    for tac in tacs do
      cmds := cmds.push <|
        ← `(macro_rules | `(tactic| trivial) => `(tactic| $tac))

    return mkNullNode cmds

    -- let cmd : TSyntax `command := { raw := mkNullNode cmds }
    -- `(command| $cmd)

setup_trivial
  decide
  tauto aesop
  linarith omega
  group abel ring

-- macro_rules | `(tactic| trivial) => `(tactic| simp <;> trivial)
-- macro_rules | `(tactic| trivial) => `(tactic| simp_all)
