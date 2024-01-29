namespace Logic

example {Q : α → Prop} : (∀ a, Q a → P) ↔ (∃ a, Q a) → P
where
  -- uncurry
  mp f pair := let ⟨a, b⟩ := pair; f a b
  -- curry
  mpr f a b := f ⟨a, b⟩

end Logic
