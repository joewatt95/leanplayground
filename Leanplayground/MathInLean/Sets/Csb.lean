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

theorem bij_of_2_inj
  {f : α → β} {g : β → α}
  (f_inj : Injective f) (g_inj : Injective g)
  : ∃ h : α → β, Bijective h :=

  let F : Set α →o Set α :=
    { toFun := λ X ↦ g '' (f '' X ᶜ)ᶜ
      monotone' := λ _X _Y ↦ by aesop }

  let S : Ordinal → Set α := OrdinalApprox.lfpApprox F ∅
  have ⟨O, _⟩ := OrdinalApprox.lfp_mem_range_lfpApprox F
  let S₀ := S O

  let h a := if _ : a ∈ S₀ then invFun g a else f a

  have := calc
        g '' (f '' S₀ᶜ)ᶜ
      = g '' (f '' (OrderHom.lfp F)ᶜ)ᶜ := by aesop
    _ = OrderHom.lfp F                 := by exact F.map_lfp
    _ = S₀                             := by aesop

  have g_surjects {a} (_ : a ∈ S₀) : ∃ b ∈ (f '' S₀ᶜ)ᶜ, g b = a :=
    have : a ∈ g '' (f '' S₀ᶜ)ᶜ := by aesop
    by rw [←mem_image]; exact this

  have : LeftInverse (invFun g) g := leftInverse_invFun g_inj
  have := calc
        (f '' S₀ᶜ)ᶜ
      = invFun g '' (g '' (f '' S₀ᶜ)ᶜ)  := by rw [this.image_image]
    _ = invFun g '' S₀                  := by aesop

  have : Surjective h := piecewise_is_surj <| calc
        invFun g '' S₀ ∪ f '' S₀ᶜ
      = (f '' S₀ᶜ)ᶜ ∪ f '' S₀ᶜ    := by aesop
    _ = univ                      := by ext _; simp only [compl_union_self, mem_univ]

  have : Injective h :=
    have := calc
          invFun g '' S₀ ∩ f '' S₀ᶜ
      _ = (f '' S₀ᶜ)ᶜ ∩ f '' S₀ᶜ    := by aesop
      _ = ∅                         := by ext _; simp only [compl_inter_self, mem_empty_iff_false]

    have : InjOn f S₀ᶜ := λ _a _ _a' _ ↦ by aesop

    have : InjOn (invFun g) S₀ :=
      λ a (_ : a ∈ S₀) a' (_ : a' ∈ S₀) (_ : invFun g a = invFun g a') ↦
        have ⟨b, _, _⟩ : ∃ b ∈ (f '' S₀ᶜ)ᶜ, g b = a := g_surjects ‹a ∈ S₀›
        have ⟨b', _, _⟩ : ∃ b' ∈ (f '' S₀ᶜ)ᶜ, g b' = a' := g_surjects ‹a' ∈ S₀›
        have := ‹LeftInverse (invFun g) g›
        calc
          a = g b                 := by aesop
          _ = g (invFun g $ g b)  := by exact b |> this |>.symm |> congr_arg g
          _ = g (invFun g a)      := by aesop
          _ = g (invFun g a')     := by aesop
          _ = g (invFun g $ g b') := by aesop
          _ = g b'                := by exact b' |> this |> congr_arg g
          _ = a'                  := by aesop

    show Injective h by apply piecewise_is_inj; repeat assumption

  ⟨h, ‹Injective h›, ‹Surjective h›⟩

end Sets
