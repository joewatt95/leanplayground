import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

import Leanplayground.MathInLean.Utils.Function

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
  : Injective <| @h _ _ f g X
  | a, a', (ha_eq_ha' : h a = h a') =>
    have {a} := Classical.em <| a ∈ X
    match this, this with
    | .inl (_ : a ∈ X), .inr (_ : a' ∉ X) => go ‹_› ‹_› ha_eq_ha'
    | .inr (_ : a ∉ X), .inl (_ : a' ∈ X) => go ‹_› ‹_› ha_eq_ha'.symm
    | .inl _, .inl _ | .inr _, .inr _ => by aesop
  where
    go {P} : ∀ {a a'}, a ∈ X → a' ∉ X → h a = h a' → P
    | a, a', _, _, _ => nomatch calc
      f a = g a'             := by aesop
        _ ∈ f '' X ∩ g '' Xᶜ := ⟨by aesop, by aesop⟩
        _ = ∅                := by assumption

lemma piecewise_is_surj
  (f_union_g_eq_univ : f '' X ∪ g '' Xᶜ = univ)
  : Surjective <| @h _ _ f g X
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
        monotone' := λ _X _Y ↦ by aesop }

    let S : Ordinal → Set α := lfpApprox F ∅
    have ⟨O, (_ : S O = lfp F)⟩ := lfp_mem_range_lfpApprox F

    let S₀ := S O
    have : g '' (f '' S₀ᶜ)ᶜ = S₀ := by
      rw [‹S₀ = lfp F›]; exact F.map_lfp

    let h a := if a ∈ S₀ then invFun g a else f a

    have : LeftInverse (invFun g) g := leftInverse_invFun g_inj

    have := calc
          (f '' S₀ᶜ)ᶜ
      _ = invFun g '' (g '' (f '' S₀ᶜ)ᶜ) := by rw [this.image_image]
      _ = invFun g '' S₀                 := by aesop

    have : Surjective h := piecewise_is_surj <| calc
          invFun g '' S₀ ∪ f '' S₀ᶜ
      _ = (f '' S₀ᶜ)ᶜ ∪ f '' S₀ᶜ    := by aesop
      _ = univ                      := by rw [compl_union_self]

    have : Injective h :=
      have := calc
            invFun g '' S₀ ∩ f '' S₀ᶜ
        _ = (f '' S₀ᶜ)ᶜ ∩ f '' S₀ᶜ    := by aesop
        _ = ∅                         := by rw [compl_inter_self]

      have : InjOn f S₀ᶜ := λ _a _ _a' _ ↦ by aesop

      have : InjOn (invFun g) S₀ :=
        λ a _ a' _ (_ : invFun g a = invFun g a') ↦
          have : ∀ x, invFun g (g x) = x := ‹LeftInverse _ _›

          have : S₀ ⊆ g '' (f '' S₀ᶜ)ᶜ := ‹g '' _ = _› |>.symm |> subset_of_eq
          have : ∀ a ∈ _, ∃ b ∈ _, g b = a := this

          have ⟨b, _, (_ : g b = a)⟩ := this _ ‹_›
          have ⟨b', _, (_ : g b' = a')⟩ := this _ ‹_›

          show a = a' by aesop

      show Injective h by apply piecewise_is_inj; repeat assumption

    exact ⟨h, ‹Injective h›, ‹Surjective h›⟩

end Sets
