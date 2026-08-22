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

private noncomputable abbrev h a := if _ : a ∈ X then f a else g a

lemma piecewise_is_inj
  (f_inj : InjOn f X) (g_inj : InjOn g Xᶜ)
  (img_inter_empty : f '' X ∩ g '' Xᶜ = ∅)
  : Injective <| h (f := f) (g := g) (X := X) :=
  let h := h (f := f) (g := g) (X := X)

  have {a} {a'} (_ : a ∈ X) (_ : a' ∉ X) : h a ≠ h a' :=
    λ _ : h a = h a' ↦
      have : h a ∈ f '' X ∩ g '' Xᶜ := by grind
      show ⊥ by grind

  show Injective h by grind [Injective, InjOn]

lemma piecewise_is_surj
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
  : ∃ h : α → β, Bijective h :=
  -- set_option trace.profiler true in
  match isEmpty_or_nonempty _ with
  -- We need to consider cases on whether β is empty because Nonempty β is
  -- required for invFun g to be well-defined.
  | .inl (_ : IsEmpty β) =>
    ⟨f, ‹Injective f›, show Surjective f from surj_of_isEmpty⟩

  | .inr (_ : Nonempty β) =>
    open OrderHom OrdinalApprox in

    let F : Set α →o Set α :=
      { toFun X := g '' (f '' Xᶜ)ᶜ
        monotone' := by grind [Monotone] }

    let S : Ordinal → Set α := lfpApprox F ∅
    have ⟨O, (_ : S O = F.lfp)⟩ := lfp_mem_range_lfpApprox _

    let S₀ := S O
    have : F S₀ = S₀ := by grind [map_lfp]
    have : g '' (f '' S₀ᶜ)ᶜ = S₀ := this

    let h a := if a ∈ S₀ then g.invFun a else f a

    have : LeftInverse g.invFun g := leftInverse_invFun ‹Injective g›
    have : g.invFun  '' S₀ = (f '' S₀ᶜ)ᶜ := by grind

    have : Surjective h :=
      have : g.invFun '' S₀ ∪ f '' S₀ᶜ = univ := by grind [compl_union_self]
      piecewise_is_surj this

    have : Injective h :=
      have : g.invFun '' S₀ ∩ f '' S₀ᶜ = ∅ := by grind [compl_inter_self]

      have : InjOn f S₀ᶜ := by grind [InjOn]

      have : InjOn g.invFun S₀ := by rw [image] at *; grind [InjOn]

      show Injective h from piecewise_is_inj ‹_› ‹_› ‹_›

    ⟨h, ‹Injective h›, ‹Surjective h›⟩

end Sets
