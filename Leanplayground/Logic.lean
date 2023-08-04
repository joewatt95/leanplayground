namespace Logic

variable {P : Prop} {Q : α → Prop}

-- CPS unpacking of existential type.
example : (∀ τ, Q τ → P) → (∃ τ, Q τ) → P :=
  λ κ ⟨τ, π⟩ => κ τ π

-- CPS packing of existential type.
example : ((∃ τ, Q τ) → P) → ∀ τ, Q τ → P :=
  λ κ τ π => κ ⟨τ, π⟩

end Logic