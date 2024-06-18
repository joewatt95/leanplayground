import Lean

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

import Auto.Tactic
import Duper
import Egg
-- import Smt

import Loogle.Find

macro "setup_auto" : command => `(
  set_option auto.smt true
  set_option auto.smt.trust true
  set_option auto.smt.solver.name "z3"

  set_option trace.auto.smt.printCommands true
  set_option trace.auto.smt.result true

  set_option auto.tptp true
  set_option auto.tptp.solver.name "zipperposition"
  set_option auto.tptp.zeport.path "/home/joe/dev/zipperposition/portfolio"
)

syntax "setup_trivial" sepBy1(tactic, ",") : command

macro_rules
  | `(setup_trivial $[$tacs:tactic],*) => do
    let mut cmds := #[← `(set_option linter.unreachableTactic false)]

    for tac in tacs do
      cmds := cmds.push <|
        ← `(macro_rules | `(tactic| trivial) => `(tactic| $tac))

    pure <| Lean.mkNullNode cmds

    -- let cmd : TSyntax `command := { raw := mkNullNode cmds }
    -- `(command| $cmd)

setup_trivial decide, tauto, aesop, omega, linarith

-- macro_rules | `(tactic| trivial) => `(tactic| simp <;> trivial)
-- macro_rules | `(tactic| trivial) => `(tactic| simp_all)
