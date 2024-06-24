import Mathlib.Tactic.SlimCheck
-- import Mathlib.Testing.SlimCheck.Testable
import Smt

namespace Commands

macro "#APPLY TACTIC" ruleName:ident tactic:tactic : command =>
  `(example : $ruleName := by unfold $ruleName; $tactic)

macro "#TEST" ruleName:ident : command =>
  `(#APPLY TACTIC $ruleName slim_check)

macro "#SMT" ruleName:ident : command =>
  `(#APPLY TACTIC $ruleName smt)

macro "#PROOF SEARCH" ruleName:ident : command =>
  `(#APPLY TACTIC $ruleName aesop)

end Commands
