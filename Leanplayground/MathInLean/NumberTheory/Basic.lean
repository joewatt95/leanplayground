import Batteries.Data.Int
import Batteries.Data.Nat

import Auto
import Duper
import Mathlib.Tactic

import Loogle.Find

namespace NumberTheory

example {m n} (_ : m.Coprime n) :
  m ^ 2 ≠ 2 * n ^ 2 :=
  have : 2 ∣ m := sorry
  sorry

end NumberTheory
