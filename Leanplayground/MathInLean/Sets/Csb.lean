import Auto
import Duper
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

-- import Loogle.Find

namespace Sets

universe u v
variable
  {α : Type u} {β : Type v} [Nonempty β]

open Classical Function Set

section piecewise_inj_surj

variable {f g : α → β} {X : Set α}

noncomputable abbrev h a := if _ : a ∈ X then f a else g a

lemma piecewise_is_inj
  (f_inj : InjOn f X)
  (g_inj : InjOn g Xᶜ)
  (f_inter_g_empty : f '' X ∩ g '' Xᶜ = ∅)
  : Injective <| @h _ _ f g X
  | a, a', (_ : h a = h a') =>
    have : (a ∈ X ∧ a' ∈ X) ∨ (a ∉ X ∧ a' ∉ X) → a = a' := by aesop

    have (_ : a ∈ X) (_ : a' ∉ X) : a = a' := nomatch calc
      f a = g a'             := by aesop
        _ ∈ f '' X ∩ g '' Xᶜ := by exact ⟨by aesop, by aesop⟩
        _ = ∅                := by assumption

    have (_ : a ∉ X) (_ : a' ∈ X) : a = a' := nomatch calc
      g a = f a'             := by aesop
        _ ∈ f '' X ∩ g '' Xᶜ := by exact ⟨by aesop, by aesop⟩
        _ = ∅                := by assumption

    show a = a' by aesop

lemma piecewise_is_surj
  (f_union_g_eq_univ : f '' X ∪ g '' Xᶜ = univ)
  : Surjective <| @h _ _ f g X
  | b =>
    have : b ∈ f '' X ∪ g '' Xᶜ := by aesop
    match this with
    | .inl _ | .inr _ => show ∃ a, h a = b by aesop

end piecewise_inj_surj

open OrderHom OrdinalApprox in
theorem bij_of_2_inj
  {f : α → β} {g : β → α}
  (f_inj : Injective f) (g_inj : Injective g)
  : ∃ h : α → β, Bijective h :=

  let F : Set α →o Set α :=
    { toFun := λ X ↦ g '' (f '' X ᶜ)ᶜ
      monotone' := λ _X _Y ↦ by aesop }

  let S : Ordinal → Set α := lfpApprox F ⊥
  have ⟨O, _⟩ := lfp_mem_range_lfpApprox F

  let S₀ := S O
  have : S₀ = lfp F := by assumption

  let h a := if _ : a ∈ S₀ then invFun g a else f a

  have : g '' (f '' S₀ᶜ)ᶜ = S₀ := by rw [‹S₀ = lfp F›]; exact F.map_lfp

  have g_surj_on : ∀ a ∈ S₀, ∃ b ∈ (f '' S₀ᶜ)ᶜ, g b = a
    | a, _ =>
      have : a ∈ g '' (f '' S₀ᶜ)ᶜ := by aesop
      by simp only [mem_image] at this; exact this

  have g_inv_left_inv : LeftInverse (invFun g) g := leftInverse_invFun g_inj

  have := calc
        (f '' S₀ᶜ)ᶜ
    _ = invFun g '' (g '' (f '' S₀ᶜ)ᶜ) := by rw [g_inv_left_inv.image_image]
    _ = invFun g '' S₀                 := by aesop

  have : Surjective h := piecewise_is_surj <| calc
        invFun g '' S₀ ∪ f '' S₀ᶜ
    _ = (f '' S₀ᶜ)ᶜ ∪ f '' S₀ᶜ    := by aesop
    _ = univ                      := by simp only [compl_union_self]

  have : Injective h :=
    have := calc
          invFun g '' S₀ ∩ f '' S₀ᶜ
      _ = (f '' S₀ᶜ)ᶜ ∩ f '' S₀ᶜ    := by aesop
      _ = ∅                         := by simp only [compl_inter_self]

    have : InjOn f S₀ᶜ := λ _a _ _a' _ ↦ by aesop

    have : InjOn (invFun g) S₀
      | a, (_ : a ∈ S₀), a', (_ : a' ∈ S₀),
        (_ : invFun g a = invFun g a') =>
        have : ∃ b ∈ (f '' S₀ᶜ)ᶜ, g b = a := g_surj_on _ ‹a ∈ S₀›
        have : ∃ b' ∈ _, g b' = a' := g_surj_on _ ‹a' ∈ S₀›
        have : ∀ x, invFun g (g x) = x := g_inv_left_inv
        show a = a' by aesop

    show Injective h by apply piecewise_is_inj; repeat assumption

  ⟨h, ‹Injective h›, ‹Surjective h›⟩

end Sets
