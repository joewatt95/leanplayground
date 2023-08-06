namespace Logic

example {Q : α → Prop} : (∀ a, Q a → P) ↔ (∃ a, Q a) → P :=
  ⟨uncurry, curry⟩
  where
    uncurry f pair := let ⟨a, b⟩ := pair; f a b
    curry f a b := f ⟨a, b⟩

end Logic