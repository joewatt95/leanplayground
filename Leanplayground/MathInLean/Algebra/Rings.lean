import Mathlib.RingTheory.Ideal.QuotientOperations

import Leanplayground.MathInLean.Utils.Finite
import Leanplayground.MathInLean.Utils.Subtype

namespace Rings

universe u v

variable
  {R : Type u} {S : Type v}
  [CommRing R] [CommRing S]

example {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq ‹I = J›

section CRT

universe w

variable {ι : Type w}

-- The homomorphism from `R ⧸ ⨅ i, I i` to `∀ i, R ⧸ I i` featured in the
-- Chinese Remainder Theorem.
-- This follows naturally from the universal properties of products and
-- coequalisers, ie Pi and quotient types.
def crtMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  -- `Pi.ringHom` allows us to use the universal property of Pi types to
  -- construct a ring morphism into a Pi type.
  let f_i : ∀ i, R →+* R ⧸ I i := (. |> I |> Ideal.Quotient.mk)
  let f : R →+* ∀ i, R ⧸ I i := Pi.ringHom f_i

  -- Lift the morphism to the quotient ring via the corresponding universal
  -- property.
  have : ⨅ i, I i = RingHom.ker f := by rw [Ideal.ker_Pi_Quotient_mk]
  have : ∀ r ∈ ⨅ i, I i, f r = 0 :=
    λ _ _ ↦ by simp_all only [f, f_i]; exact ‹_›

  Ideal.Quotient.lift _ _ this

lemma crtMap_mk {I : ι → Ideal R} {r : R} :
  crtMap I ⟦r⟧ = λ i ↦ (⟦r⟧ : R ⧸ I i) := rfl

lemma crtMap_mk' {I : ι → Ideal R} {r : R} {i : ι} :
  crtMap I ⟦r⟧ i = (⟦r⟧ : R ⧸ I i) := rfl

lemma crtMap_inj {I : ι → Ideal R}
  : Function.Injective <| crtMap I :=
  Ideal.injective_lift_iff (crtMap.proof_3 _ <| crtMap.proof_2 _)
    |>.mpr <| by rw [crtMap.proof_2]

section

variable  {I : Ideal R} {J : ι → Ideal R}

open Classical in
theorem add_Inf_eq_one_of_forall_add_eq_one {s : Finset ι}
  (_ : ∀ j ∈ s, I + J j = 1)
  : I + ⨅ j ∈ s, J j = 1 :=
  -- set_option trace.profiler true in
  suffices 1 ≤ I + ⨅ j ∈ s, J j by
    simp_all only [Submodule.add_eq_sup, Ideal.one_eq_top, top_le_iff]

  match s.eq_empty_or_nonempty with
  | .inl (_ : s = ∅) => by simp [‹s = ∅›]
  | .inr ⟨i, (_ : i ∈ s)⟩ =>
    let i : s := ↓i

    have : I + J i = 1 := ‹∀ j ∈ s, I + J j = 1› _ ‹_›

    let s' := s.erase i
    let K := ⨅ j ∈ s', J j

    -- Well-founded recusion on s', via the ordering induced by finset cardinality.
    have : I + K = 1 :=
      have : s'.card < s.card := Finset.card_erase_lt_of_mem ‹_›
      have : ∀ j ∈ s', I + J j = 1 := by simp_all [s']
      add_Inf_eq_one_of_forall_add_eq_one this

    calc
      1 = I + K * (I + J i)     := by simp [‹I + K = 1›, ‹I + J i = 1›]
      _ = (I + K * I) + K * J i := by ring
      _ = I + K * J i           := by simp only [Submodule.add_eq_sup, Ideal.sup_mul_left_self]
      _ ≤ I + K ⊓ J i           := add_le_add_left Ideal.mul_le_inf _
      _ = I + ⨅ j ∈ s, J j      := by rw [inf_comm, Finite.Finset.iInf_erase]

termination_by s.card

theorem isCoprime_Inf {s : Finset ι}
  : (∀ j ∈ s, IsCoprime I <| J j) → IsCoprime I (⨅ j ∈ s, J j) := by
  simp only [Ideal.isCoprime_iff_add]
  exact add_Inf_eq_one_of_forall_add_eq_one

end

-- #check IsCoprime
-- #check Ideal.isCoprime_iff_add
-- #check Ideal.isCoprime_iff_exists
-- #check Ideal.isCoprime_iff_sup_eq
-- #check Ideal.isCoprime_iff_codisjoint

-- #check Ideal.quotientInfToPiQuotient_surj

section

variable
  [Fintype ι] {I : ι → Ideal R}
  (hI_pairwise_coprime : ∀ i j, i ≠ j → IsCoprime (I i) (I j))

open Classical in
-- set_option trace.profiler true in
theorem crtMap_surj : Function.Surjective <| crtMap I :=
  -- set_option trace.profiler true in
  λ _ : ∀ i, R ⧸ I i ↦
    have : ∀ i, ∃ r : R, (r : R ⧸ I i) = ‹∀ i, R ⧸ I i› i :=
      λ _ ↦ Quot.exists_rep _
    have ⟨
      (choiceFn : ι → R),
      (_ : ∀ i, (choiceFn i : R ⧸ I i) = ‹∀ i, R ⧸ I i› i)
    ⟩ := axiomOfChoice this

    have : ∀ i,
      ∃ r : R, (r : R ⧸ I i) = 1 ∧
      ∀ j ≠ i, (r : R ⧸ I j) = 0 :=
      λ i ↦
        let s := Finset.univ.erase i

        have : ∀ j ∈ s, IsCoprime (I i) <| I j :=
          λ _ _ ↦ by simp_all only
            [ Ne.symm, ne_eq, Finset.mem_erase, Finset.mem_univ, and_true,
              not_false_eq_true, s ]
        have : IsCoprime (I i) <| ⨅ j ∈ s, I j := isCoprime_Inf this
        have ⟨
          r', (_ : r' ∈ I i),
          r, (_ : r ∈ ⨅ j ∈ s, I j),
          (_ : r' + r = 1)
        ⟩ := Ideal.isCoprime_iff_exists.mp this

        have : (r' : R ⧸ I i) = 0 :=
          ‹r' ∈ I i› |> (Submodule.Quotient.mk_eq_zero _).mpr
        have := calc
              (r' : R ⧸ I i) + r
          _ = ⟦r' + r⟧           := rfl
          _ = (1 : R ⧸ I i)     := by congr
        have : (r : R ⧸ I i) = 1 := by simp_all only [zero_add]

        have : ∀ j ≠ i, r ∈ I j :=
          λ _ _ ↦ by simp_all only
            [ ne_eq, Finset.mem_erase, Finset.mem_univ, and_true,
              Ideal.mem_iInf, zero_add, not_false_eq_true, s ]
        have : ∀ j ≠ i, (r : R ⧸ I j) = 0 :=
          have : ∀ {j}, (r : R ⧸ I j) = 0 ↔ r ∈ I j :=
            Submodule.Quotient.mk_eq_zero _
          by simp_all only [ne_eq, not_false_eq_true, implies_true]

        ⟨r, ‹(r : R ⧸ I i) = 1›, ‹∀ j ≠ i, (r : R ⧸ I j) = 0›⟩

    have ⟨
      (choiceFn' : ι → R),
      (_ : ∀ i,
        (choiceFn' i : R ⧸ I i) = 1 ∧
        ∀ j ≠ i, (choiceFn' i : R ⧸ I j) = 0)
    ⟩ := axiomOfChoice this

    let r := ∑ i, choiceFn i * choiceFn' i

    suffices ∀ i, crtMap _ (r : R ⧸ ⨅ i, I i) i = ‹∀ i, R ⧸ I i› i from
      ⟨r, funext this⟩

    have : ∀ {i}, ∀ j ≠ i, (choiceFn j : R ⧸ I i) * choiceFn' j = 0 := by
      simp_all only [ne_eq, not_false_eq_true, Ne.symm, mul_zero, implies_true]

    λ i ↦ calc
          crtMap _ (r : R ⧸ ⨅ i, I i) i
      _ = ∑ j, (choiceFn j : R ⧸ I i) * choiceFn' j := by simp_all only [map_sum, map_mul, Finset.sum_apply, r]; rfl
      _ = (choiceFn i : R ⧸ I i) * choiceFn' i      := Fintype.sum_eq_single _ this
      _ = ‹∀ i, R ⧸ I i› i * 1                      := by simp_all only
      _ = ‹∀ i, R ⧸ I i› i                          := mul_one _

theorem crtMap_bij : Function.Bijective <| crtMap I :=
  ⟨crtMap_inj, crtMap_surj hI_pairwise_coprime⟩

noncomputable def crtIso : R ⧸ ⨅ i, I i ≃+* ∀ i, R ⧸ I i :=
  let crtEquiv : R ⧸ ⨅ i, I i ≃ Π i, R ⧸ I i :=
    Equiv.ofBijective _ <| crtMap_bij hI_pairwise_coprime
  { crtMap I, crtEquiv with }

end

end CRT

end Rings
