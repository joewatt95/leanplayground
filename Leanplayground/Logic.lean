namespace Logic

variable {P : Prop} {Q : α → Prop}

-- CPS unpacking of existential type.
example : (∀ τ, Q τ → P) → (∃ τ, Q τ) → P :=
  λ κ ⟨τ, h⟩ => κ τ h

-- CPS packing of existential type.
example : ((∃ τ, Q τ) → P) → ∀ τ, Q τ → P :=
  λ κ τ h => κ ⟨τ, h⟩

end Logic