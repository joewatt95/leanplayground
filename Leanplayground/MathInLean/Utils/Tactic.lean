import Mathlib.Tactic.Common

import Auto.Tactic
import Duper
import Egg
import Smt

import Loogle.Find

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

set_option auto.tptp true

macro_rules | `(tactic| trivial) => `(tactic| tauto)

macro_rules | `(tactic| trivial) => `(tactic| simp <;> trivial)
macro_rules | `(tactic| trivial) => `(tactic| simp_all)

macro_rules | `(tactic| trivial) => `(tactic| aesop)

macro_rules | `(tactic| trivial) => `(tactic| omega)
macro_rules | `(tactic| trivial) => `(tactic| linarith)
