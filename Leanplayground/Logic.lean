namespace Logic

variable {P : Prop} {Q : α → Prop}

example : (∀ τ, Q τ → P) → (∃ τ, Q τ) → P :=
  λ h ⟨τ, hQa⟩ => h τ hQa

example : ((∃ τ, Q τ) → P) → ∀ τ, Q τ → P :=
  λ h τ hQa => h ⟨τ, hQa⟩

end Logic