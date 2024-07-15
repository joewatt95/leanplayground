import Leanplayground.MathInLean.Utils.Tactic

namespace Logic

variable {p q r : Prop}

lemma curry (_ : p ∧ q → r) (_ : p) (_ : q) : r := ‹p ∧ q → r› ⟨‹p›, ‹q›⟩

lemma uncurry : (p → q → r) → (p ∧ q) → r := And.elim

end Logic
