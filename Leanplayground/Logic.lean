import Aesop
-- import Auto.Tactic
-- import Duper

namespace Logic

example {Q : α → Prop} : (∀ a, Q a → P) ↔ (∃ a, Q a) → P
where
  -- uncurry
  mp f pair := let ⟨a, b⟩ := pair; f a b
  -- curry
  mpr f a b := f ⟨a, b⟩

example {drunk : α → Prop} [Inhabited α] : ∃ x, drunk x → ∀ x, drunk x :=
  match Classical.em _ with
  | .inl (h : ∀ x, drunk x) =>
    have : drunk default → ∀ x, drunk x := by aesop
    show ∃ _, _ from ⟨default, this⟩

  | .inr _ =>
    have ⟨x, h_not_drunk_x⟩ : ∃ x, ¬ drunk x := by aesop
    have : drunk x → ∀ x, drunk x := by aesop
    show ∃ _, _ from ⟨x, this⟩

end Logic
