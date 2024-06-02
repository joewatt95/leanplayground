import Leanplayground.MathInLean.Utils.Tactic

namespace Logic

variable {p q r : Prop}

lemma curry (_ : p ∧ q → r) (_ : p) (_ : q) : r := by tauto

lemma uncurry (_ : p → q → r) (_ : p ∧ q) : r := by tauto

end Logic
