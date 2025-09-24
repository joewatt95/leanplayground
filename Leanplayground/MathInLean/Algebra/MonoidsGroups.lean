import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Finite

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
      have : x⁻¹ = g * h⁻¹ * g⁻¹ := by rw [‹x = _›]; group
      show φ x⁻¹ by
        duper [this, ‹h ∈ H›, Subgroup.inv_mem] {portfolioInstance := 1}
  }

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
        H = ⊥
    _ ↔ ∀ g ∈ H, g = 1     := Subgroup.eq_bot_iff_forall _
    _ ↔ ∀ h h' : H, h = h' := ⟨go, by aesop⟩
    _ ↔ Fintype.card H ≤ 1 := by rw [Fintype.card_le_one_iff]
    _ ↔ Fintype.card H = 1 := by omega
  where
    go : (∀ g ∈ H, g = 1) → ∀ h h' : {g // g ∈ H}, h = h' :=
      λ _ ⟨h, (_ : h ∈ H)⟩ ⟨h', (_ : h' ∈ H)⟩ ↦
        Subtype.ext <| show h = h' by duper [*] {portfolioInstance := 1}

lemma inf_bot_of_coprime {H K : Subgroup G} [Fintype G] [Fintype H] [Fintype K]
  (h : Fintype.card H |>.Coprime (Fintype.card K))
  : H ⊓ K = ⊥ :=
  let HK := H ⊓ K
  have : Fintype HK := Fintype.ofFinite _

  suffices Fintype.card HK = 1 from eq_bot_iff_card.mpr this

  have : Nat.card HK ∣ (Nat.card H).gcd (Nat.card K) := by
    duper [go, Subgroup.card_dvd_of_le, Nat.dvd_gcd_iff]
      {portfolioInstance := 1}

  show Fintype.card HK = 1 by
    simp_all only [Nat.card_eq_fintype_card, Nat.dvd_one]
  where
    go : H ⊓ K ≤ H ∧ H ⊓ K ≤ K := le_inf_iff.mp <| le_refl _

instance : MulAction G (Subgroup G) where
  smul := conjugate

  one_smul (H : Subgroup G) :=
    show conjugate 1 H = H by simp only [conjugate]; aesop

  mul_smul g g' (H : Subgroup G) :=
    let lhs := H |> conjugate (g * g')
    let rhs := H |> conjugate g' |> conjugate g

    suffices ∀ x : G, x ∈ lhs ↔ x ∈ rhs from Subgroup.ext this

    have : ∀ h, (g * g') * h * (g * g')⁻¹ = g * (g' * h * g'⁻¹) * g⁻¹ :=
      λ _ ↦ by group

    λ x ↦ show x ∈ lhs ↔ x ∈ rhs by
      simp only [conjugate, Subgroup.mem_mk, lhs, rhs]
      aesop

variable {H K : Subgroup G}

-- Note that:
-- - `orbit_subgroup_eq_rightCoset` says that for `g : G`, `g • H = orbit H g`,
--   ie the coset gH is the orbit of the left action of Hᵒᵖ (ie right actions of H)
--   on g.
-- - `G ⧸ H ⟶βδ* Quotient (MulAction.orbitRel H.op G)`
--   This is the quotient type formed by quotiening out the Setoid `orbitRel`,'
--   which is the equivalence relation of being in the same orbit.
--   Thanks to `orbit_subgroup_eq_rightCoset`, `orbitRel H.op G` is equivalent
--   to saying that the elements in each partition belong to the same coset.
--   In other words, `G ⧸ H` is the type of equivalence classes of orbits of
--   the action of H (= left cosets of H in G).

open MulAction

noncomputable def lagrange : G ≃ (G ⧸ H) × H :=
  let H' : G ⧸ H := (1 : G)

  have : G ≃ orbit G H' × stabilizer G H' :=
    orbitProdStabilizerEquivGroup _ _ |>.symm

  have : orbit G H' ≃ G ⧸ H :=
    Equiv.subtypeUnivEquiv <| by
      simp only [mem_orbit_iff, Quotient.smul_mk, smul_eq_mul, mul_one, H']
      exact Quotient.exists_rep

  have : stabilizer G H' = H := stabilizer_quotient _
  have : stabilizer G H' ≃ H := by rw [this]

  calc
    G ≃ orbit G H' × stabilizer G H' := ‹_›
    _ ≃ (G ⧸ H) × H                  := Equiv.prodCongr ‹_› ‹_›

theorem lagrange'
  : Nat.card G = Nat.card (G ⧸ H) * Nat.card H := by
  rw [←Nat.card_prod, Nat.card_congr lagrange]

variable [Fintype G]

lemma aux_card_eq
  (h' : Nat.card G = Nat.card H * Nat.card K)
  : Nat.card (G ⧸ H) = Nat.card K :=
  have : Nat.card H * Nat.card (G ⧸ H) = Nat.card H * Nat.card K := by
    duper [h', lagrange', Nat.mul_comm] {portfolioInstance := 1}
  by aesop

variable
  [H.Normal] [K.Normal]
  (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

-- #check Fintype.bijective_iff_injective_and_card
-- #check MonoidHom.ker_eq_bot_iff
-- #check MonoidHom.restrict
-- #check MonoidHom.ker_restrict

noncomputable def iso₁ : K ≃* G ⧸ H where
  toFun k :=
    sorry

  invFun := sorry

  left_inv := sorry

  right_inv := sorry

  map_mul' := sorry

end Algebra
