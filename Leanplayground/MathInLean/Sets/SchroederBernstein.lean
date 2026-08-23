import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

import Leanplayground.MathInLean.Utils.Tactic

namespace Sets

universe u v
variable {α : Type u} {β : Type v}

open Classical Function Set

section piecewise_inj_surj

variable {f g : α → β} {X : Set α}

private noncomputable abbrev h a := if _ : a ∈ X then f a else g a

lemma inj_of_piecewise
  (f_inj : InjOn f X) (g_inj : InjOn g Xᶜ)
  (img_inter_empty : f '' X ∩ g '' Xᶜ = ∅)
  : Injective <| h (f := f) (g := g) (X := X) :=
  let h := h

  have {a a'} (_ : a ∈ X) (_ : a' ∉ X) : h a ≠ h a' :=
    λ _ : h a = h a' ↦
      have : h a ∈ f '' X ∩ g '' Xᶜ := by grind
      show ⊥ by grind

  show Injective h by grind [Injective, InjOn]

lemma surj_of_piecewise
  (f_union_g_eq_univ : f '' X ∪ g '' Xᶜ = univ)
  : Surjective <| h (f := f) (g := g) (X := X) :=
  λ b ↦
    have : b ∈ f '' X ∪ g '' Xᶜ := by grind
    show ∃ a, h a = b by grind

end piecewise_inj_surj

-- set_option trace.profiler true in
theorem schroeder_bernstein
  {f : α → β} {g : β → α}
  (f_inj : Injective f) (g_inj : Injective g)
  : ∃ h : α → β, Bijective h := by
  -- set_option trace.profiler true in
  -- We need to consider cases on whether β is empty because Nonempty β is
  -- required for invFun g to be well-defined.
  if _ : IsEmpty β then exact ⟨f, Bijective.of_isEmpty _⟩
  else open OrderHom OrdinalApprox in
    have : Nonempty β := by grind [not_isEmpty_iff]
    have : LeftInverse g.invFun g := leftInverse_invFun ‹Injective g›

    let F : Set α →o Set α := {
      toFun X := g '' (f '' Xᶜ)ᶜ
      monotone' := by grind [Monotone]
    }

    let S : Ordinal → Set α := lfpApprox F ∅
    have ⟨O, (_ : S O = F.lfp)⟩ := lfp_mem_range_lfpApprox _

    let S₀ := S O
    have : g '' (f '' S₀ᶜ)ᶜ = S₀ := show F S₀ = S₀ by grind [map_lfp]

    let h a := if a ∈ S₀ then g.invFun a else f a
    refine ⟨h, ?injective, ?surjective⟩

    case surjective =>
      have : g.invFun '' S₀ ∪ f '' S₀ᶜ = univ := by grind [compl_union_self]
      exact surj_of_piecewise this

    case injective =>
      have : g.invFun '' S₀ ∩ f '' S₀ᶜ = ∅ := by grind [compl_inter_self]
      have : InjOn f S₀ᶜ := by grind [InjOn]
      have : InjOn g.invFun S₀ := by rw [image] at *; grind [InjOn]
      apply inj_of_piecewise <;> assumption

end Sets
