-- import Auto
-- import Duper
-- import Egg

import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

-- Import this below mathlib so that Loogle's #find shadows mathlib's
-- import Loogle.Find

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
  (f_inter_g_empty : f '' X ∩ g '' Xᶜ = ∅)
  : Injective <| @h _ _ f g X
  | a, a', (ha_eq_ha' : h a = h a') =>
    match Classical.em (a ∈ X), Classical.em (a' ∈ X) with
    | .inl (_ : a ∈ X), .inr (_ : a' ∉ X) => nomatch go ‹_› ‹_› ha_eq_ha'
    | .inr (_ : a ∉ X), .inl (_ : a' ∈ X) => nomatch go ‹_› ‹_› ha_eq_ha'.symm
    | .inl _, .inl _ | .inr _, .inr _ => by aesop
  where
    go : ∀ {a a'}, a ∈ X → a' ∉ X → ¬ h a = h a'
    | a, a', _, _, _ => calc
      f a = g a'             := by aesop
        _ ∈ f '' X ∩ g '' Xᶜ := by exact ⟨by aesop, by aesop⟩
        _ = ∅                := by assumption

lemma piecewise_is_surj
  (f_union_g_eq_univ : f '' X ∪ g '' Xᶜ = univ)
  : Surjective <| @h _ _ f g X
  | b =>
    have : b ∈ f '' X ∪ g '' Xᶜ := by aesop
    match this with
    | .inl _ | .inr _ => show ∃ a, h a = b by aesop

end piecewise_inj_surj

theorem bij_of_2_inj
  {f : α → β} {g : β → α}
  (f_inj : Injective f) (g_inj : Injective g)
  : ∃ h : α → β, Bijective h :=
  match isEmpty_or_nonempty β with
  -- We need to consider cases on whether β is empty because Nonempty β is
  -- required for invFun g to be well-defined.
  | .inl (_ : IsEmpty β) =>
    ⟨f, ‹Injective f›, show Surjective f from surj_of_isEmpty⟩

  | .inr (_ : Nonempty β) =>
    open OrderHom OrdinalApprox in

    let F : Set α →o Set α :=
      { toFun := λ X ↦ g '' (f '' X ᶜ)ᶜ
        monotone' := λ _X _Y ↦ by aesop }

    let S : Ordinal → Set α := lfpApprox F ∅
    have ⟨O, _⟩ := lfp_mem_range_lfpApprox F

    let S₀ := S O
    have : g '' (f '' S₀ᶜ)ᶜ = S₀ := by rw [‹S₀ = lfp F›]; exact F.map_lfp

    let h a := if _ : a ∈ S₀ then invFun g a else f a

    have : LeftInverse (invFun g) g := leftInverse_invFun g_inj

    have := calc
          (f '' S₀ᶜ)ᶜ
      _ = invFun g '' (g '' (f '' S₀ᶜ)ᶜ) := by rw [‹LeftInverse _ _›.image_image]
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
      | a, _, a', _,
        (_ : invFun g a = invFun g a') =>
        have : ∀ x, invFun g (g x) = x := ‹LeftInverse _ _›

        have : S₀ ⊆ g '' (f '' S₀ᶜ)ᶜ := ‹g '' _ = _› |>.symm |> subset_of_eq
        have : ∀ a ∈ _, ∃ b ∈ _, g b = a := this

        have ⟨b, _, (_ : g b = a)⟩ := this _ ‹_›
        have ⟨b', _, (_ : g b' = a')⟩ := this _ ‹_›

        show a = a' by aesop

      show Injective h by apply piecewise_is_inj; repeat assumption

    ⟨h, ‹Injective h›, ‹Surjective h›⟩

end Sets
