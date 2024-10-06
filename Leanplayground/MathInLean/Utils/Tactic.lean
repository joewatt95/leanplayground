import Lean

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

import Auto
import Duper
import Egg
import Smt
-- import Smt.Real

import LeanSearchClient
import Loogle.Find

macro "setup_auto" : command =>
  `(set_option auto.smt true
    set_option auto.smt.trust true
    set_option auto.smt.solver.name "z3"

    set_option trace.auto.smt.printCommands true
    set_option trace.auto.smt.result true

    set_option auto.tptp true
    set_option auto.tptp.solver.name "zipperposition"
    set_option auto.tptp.zeport.path "/home/joe/dev/zipperposition/portfolio")

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
