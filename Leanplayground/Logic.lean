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

example {drunk : α → Prop} [Nonempty α] : ∃ x, drunk x → ∀ x, drunk x :=
  match Classical.em _ with
  | .inl (_ : ∀ x, drunk x) =>
    have ⟨a⟩ := ‹Nonempty α›
    have : drunk a → ∀ x, drunk x := by aesop
    show ∃ _, _ from ⟨a, this⟩

  | .inr (_ : ¬ ∀ x, drunk x) =>
    have ⟨x, (_ : ¬ drunk x)⟩ : ∃ x, ¬ drunk x := by aesop
    have : drunk x → ∀ x, drunk x := by aesop
    show ∃ _, _ from ⟨x, this⟩

end Logic
