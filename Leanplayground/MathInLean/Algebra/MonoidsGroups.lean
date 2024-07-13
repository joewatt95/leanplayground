import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Coset
-- import Mathlib.GroupTheory.Exponent
-- import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Data.Fintype.Card

import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

import Leanplayground.MathInLean.Utils.Tactic

namespace Algebra

universe u

variable {G : Type u} [Group G]

def conjugate (g : G) (H : Subgroup G) : Subgroup G :=
  let φ x := ∃ h ∈ H, x = g * h * g⁻¹
  { carrier := {x | φ x}
    mul_mem' := by aesop
    one_mem' := by aesop
    inv_mem' := λ {x} (_ : φ x) ↦
      have ⟨h, (_ : h ∈ H), (_ : x = g * h * g⁻¹)⟩ := ‹φ x›
      let y := g * h⁻¹ * g⁻¹
      suffices x⁻¹ = y by aesop
      have : x * y = 1 := by aesop
      by duper [this, eq_inv_of_mul_eq_one_right]
  }

lemma eq_bot_iff_card {H : Subgroup G} [Fintype H] :
  H = ⊥ ↔ Fintype.card H = 1 :=
  have : 0 < Fintype.card H := Fintype.card_pos
  calc
    H = ⊥ ↔ ∀ g ∈ H, g = 1     := by exact Subgroup.eq_bot_iff_forall _
        _ ↔ ∀ h h' : H, h = h' := ⟨go, by aesop⟩
        _ ↔ Fintype.card H ≤ 1 := by egg [Fintype.card_le_one_iff]
        _ ↔ Fintype.card H = 1 := by omega
  where
    go : (∀ g ∈ H, g = 1) → ∀ h h' : H, h = h' :=
      λ _ ⟨h, (_ : h ∈ H)⟩ ⟨h', (_ : h' ∈ H)⟩ ↦ by
        apply Subtype.ext; duper [*] {portfolioInstance := 1}

lemma inf_bot_of_coprime {H K : Subgroup G} [Fintype H] [Fintype K]
  (h : Fintype.card H |>.Coprime (Fintype.card K))
  : H ⊓ K = ⊥ :=
  let HK : Type u := ↑(H ⊓ K)
  have : Fintype HK := Fintype.ofFinite _

  suffices Nat.card HK = 1 by
    simpa only [eq_bot_iff_card, Nat.card_eq_fintype_card]

  have : Nat.card HK ∣ (Nat.card H).gcd (Nat.card K) := by
    duper [go, Subgroup.card_dvd_of_le, Nat.dvd_gcd_iff]
      {portfolioInstance := 1}

  show Nat.card HK = 1 by aesop
  where
    go : H ⊓ K ≤ H ∧ H ⊓ K ≤ K := by aesop

end Algebra
