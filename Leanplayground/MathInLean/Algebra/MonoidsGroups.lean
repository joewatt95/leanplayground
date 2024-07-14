import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Coset

import Mathlib.Data.Fintype.Card

-- import Mathlib.Tactic.Group
-- import Mathlib.Tactic.Abel

import Leanplayground.MathInLean.Utils.Tactic

namespace Algebra

universe u v w

variable
  {G : Type u} {H : Type v} {K : Type w}
  [Group G] [Group H] [Group K]

def conjugate (g : G) (H : Subgroup G) : Subgroup G :=
  let φ x := ∃ h ∈ H, x = g * h * g⁻¹
  { carrier := setOf φ
    mul_mem' := by aesop
    one_mem' := by aesop
    inv_mem' := λ {x} (_ : φ x) ↦
      have ⟨h, (_ : h ∈ H), (_ : x = g * h * g⁻¹)⟩ := ‹φ x›
      let y := g * h⁻¹ * g⁻¹
      have : x * y = 1 := by aesop
      have : x⁻¹ = y := DivisionMonoid.inv_eq_of_mul _ _ this
      show φ x⁻¹ by aesop }

example {φ : G →* H} {S T : Subgroup H} (hST : S ≤ T)
  : S.comap φ ≤ T.comap φ :=
  λ g (_ : g ∈ S.comap φ) ↦
    have ⟨h, _, _⟩ : ∃ h ∈ S, φ g = h := by tauto
    have : h ∈ T := by tauto
    have : ∃ h ∈ T, φ g = h := by tauto
    show g ∈ T.comap φ by tauto

example {φ : G →* H} {ψ : H →* K} {S : Subgroup G}
  : S.map (ψ.comp φ) = (S.map φ).map ψ :=
  Subgroup.ext λ k ↦ calc
        k ∈ S.map (ψ.comp φ)
    _ ↔ ∃ s ∈ S, ψ (φ s) = k := by simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
    _ ↔ k ∈ (S.map φ).map ψ  := by simp only [Subgroup.mem_map, exists_exists_and_eq_and]

lemma eq_bot_iff_card {H : Subgroup G} [Fintype H]
  : H = ⊥ ↔ Fintype.card H = 1 :=
  have : 0 < Fintype.card H := Fintype.card_pos
  calc
    H = ⊥ ↔ ∀ g ∈ H, g = 1     := by exact Subgroup.eq_bot_iff_forall _
        _ ↔ ∀ h h' : H, h = h' := ⟨go, by aesop⟩
        _ ↔ Fintype.card H ≤ 1 := by egg [Fintype.card_le_one_iff]
        _ ↔ Fintype.card H = 1 := by omega
  where
    go : (∀ g ∈ H, g = 1) → ∀ h h' : {g // g ∈ H}, h = h' :=
      λ _ ⟨h, (_ : h ∈ H)⟩ ⟨h', (_ : h' ∈ H)⟩ ↦
        Subtype.ext <| show h = h' by duper [*] {portfolioInstance := 1}

lemma inf_bot_of_coprime {H K : Subgroup G} [Fintype H] [Fintype K]
  (h : Fintype.card H |>.Coprime (Fintype.card K))
  : H ⊓ K = ⊥ :=
  let HK := ↑(H ⊓ K)
  have : Fintype HK := Fintype.ofFinite _

  suffices Fintype.card HK = 1 from eq_bot_iff_card.mpr this

  have : Nat.card HK ∣ (Nat.card H).gcd (Nat.card K) := by
    duper [go, Subgroup.card_dvd_of_le, Nat.dvd_gcd_iff]
      {portfolioInstance := 1}

  show Fintype.card HK = 1 by
    simp_all only [Nat.card_eq_fintype_card, Nat.dvd_one]
  where
    go : H ⊓ K ≤ H ∧ H ⊓ K ≤ K := le_inf_iff.mp <| le_refl _

end Algebra
