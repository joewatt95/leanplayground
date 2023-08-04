namespace Logic

example {P : Prop} {Q : α → Prop} : (∀ τ, Q τ → P) ↔ ((∃ τ, Q τ) → P) :=
  ⟨uncurry, curry⟩
  where
    curry f a b := f ⟨a, b⟩
    uncurry f pair :=
      let ⟨a, b⟩ := pair
      f a b

end Logic