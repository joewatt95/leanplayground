import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

import Leanplayground.MathInLean.Utils.Function
import Leanplayground.MathInLean.Utils.Tactic

namespace Sets

universe u v
variable {α : Type u} {β : Type v}

open Classical Function Set

section piecewise_inj_surj

variable {f g : α → β} {X : Set α}

noncomputable abbrev h a := if _ : a ∈ X then f a else g a

lemma piecewise_is_inj
  (f_inj : InjOn f X)
  (g_inj : InjOn g Xᶜ)
  (img_inter_empty : f '' X ∩ g '' Xᶜ = ∅)
  : Injective <| h (f := f) (g := g) (X := X) :=
  let h := h (f := f) (g := g) (X := X)

  have : ∀ a ∈ X, ∀ a' ∉ X, h a ≠ h a' :=
    λ a _ a' _ (_ : h a = h a') ↦
      show ⊥ from calc
        f a = g a'             := by aesop
          _ ∈ f '' X ∩ g '' Xᶜ := ⟨by aesop, by aesop⟩
          _ = ∅                := ‹_›

  λ a a' (_ : h a = h a') ↦
    have : (a ∈ X ∧ a' ∈ X) ∨ (a ∉ X ∧ a' ∉ X) := by
      duper [*] {portfolioInstance := 7}
    show a = a' by aesop

lemma piecewise_is_surj
  (f_union_g_eq_univ : f '' X ∪ g '' Xᶜ = univ)
  : Surjective <| h (f := f) (g := g) (X := X)
  | b =>
    have : b ∈ f '' X ∪ g '' Xᶜ := by aesop
    match this with
    | .inl _ | .inr _ => show ∃ a, h a = b by aesop

end piecewise_inj_surj

theorem schroeder_bernstein
  {f : α → β} {g : β → α}
  (f_inj : Injective f) (g_inj : Injective g)
  : ∃ h : α → β, Bijective h := by
  match isEmpty_or_nonempty _ with
  -- We need to consider cases on whether β is empty because Nonempty β is
  -- required for invFun g to be well-defined.
  | .inl (_ : IsEmpty β) =>
    exact ⟨f, ‹Injective f›, show Surjective f from surj_of_isEmpty⟩

  | .inr (_ : Nonempty β) =>
    open OrderHom OrdinalApprox in

    let F : Set α →o Set α :=
      { toFun := λ X ↦ g '' (f '' X ᶜ)ᶜ
        monotone' := λ _ ↦ by aesop }

    let S : Ordinal → Set α := lfpApprox F ∅
    have ⟨O, (_ : S O = lfp F)⟩ := lfp_mem_range_lfpApprox F

    let S₀ := S O
    have : F S₀ = S₀ := by aesop
    have : g '' (f '' S₀ᶜ)ᶜ = S₀ := this

    let h a := if a ∈ S₀ then invFun g a else f a

    have : LeftInverse (invFun g) g := leftInverse_invFun ‹Injective g›
    have : invFun g '' S₀ = (f '' S₀ᶜ)ᶜ := by egg [*, this.image_image]

    have : Surjective h :=
      have : invFun g '' S₀ ∪ f '' S₀ᶜ = univ := by egg [this, compl_union_self]
      piecewise_is_surj this

    have : Injective h :=
      have : invFun g '' S₀ ∩ f '' S₀ᶜ = ∅ := by egg [*, compl_inter_self]

      have : InjOn f S₀ᶜ := λ _ ↦ by aesop

      have : InjOn (invFun g) S₀ :=
        λ a _ a' _ (_ : invFun g a = invFun g a') ↦
          have : ∀ {x}, invFun g (g x) = x := ‹LeftInverse _ _›

          have : S₀ ⊆ g '' (f '' S₀ᶜ)ᶜ := Eq.subset <| by egg [*]
          have : ∀ a ∈ S₀, ∃ b ∈ (f '' S₀ᶜ)ᶜ, g b = a := this

          have ⟨b, _, (_ : g b = a)⟩ := this _ ‹_›
          have ⟨b', _, (_ : g b' = a')⟩ := this _ ‹_›

          show a = a' by egg [*]

      show Injective h from piecewise_is_inj ‹_› ‹_› ‹_›

    exact ⟨h, ‹Injective h›, ‹Surjective h›⟩

end Sets
