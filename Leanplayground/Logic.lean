namespace Logic

variable {P : α → Prop} {Q : α → β → Prop}

example (h : ∀ a b, Q a b → P a) : ∀ a, (∃ b, Q a b) → P a:=
  λ a ⟨_b, h_Qab⟩ => (h _ _ h_Qab : P a)

example (h : ∀ a, (∃ b, Q a b) → P a) : ∀ a b, Q a b → P a :=
  λ a b h_Qab =>
    let this : ∃ b, Q a b := ⟨b, h_Qab⟩
    (h _ this : P a)

end Logic