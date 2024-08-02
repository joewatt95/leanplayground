import Mathlib.RingTheory.Ideal.QuotientOperations

import Leanplayground.MathInLean.Utils.Finite
import Leanplayground.MathInLean.Utils.Subtype

namespace Ring

universe u v

variable
  {R : Type u} {S : Type v}
  [CommRing R] [CommRing S]

example {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq ‹I = J›

section CRT

universe w
variable {ι : Type w}

-- #check Ideal.quotientInfToPiQuotient
-- #check Pi.ringHom
-- #check Ideal.keor_Pi_Quotient_mk

-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``∀ i, R ⧸ I i`` featured in the
-- Chinese Remainder Theorem.
-- This follows naturally from the universal properties of products and coequalisers.
def crtMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  -- `Pi.ringHom` allows us to use the universal property of Pi types to
  -- construct a ring morphism into a Pi type.
  let f_i : ∀ i, R →+* R ⧸ I i := (. |> I |> Ideal.Quotient.mk)
  let f : R →+* ∀ i, R ⧸ I i := Pi.ringHom f_i

  -- Lift the morphism to the quotient ring via the corresponding universal
  -- property.
  have : ⨅ i, I i = RingHom.ker f := by rw [Ideal.ker_Pi_Quotient_mk _]
  have : ∀ r ∈ ⨅ i, I i, f r = 0 := by aesop
  Ideal.Quotient.lift _ _ this

@[simp]
lemma crtMap_mk {I : ι → Ideal R} {r : R} :
  crtMap I ⟦r⟧ = λ i ↦ (⟦r⟧ : R ⧸ I i) := rfl

@[simp]
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

lemma crtMap_surj [Fintype ι] {I : ι → Ideal R}
  (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j))
  : Function.Surjective (crtMap I) :=
  λ g : ∀ i : ι, R ⧸ I i ↦
    have : ∀ i, ∃ r, Ideal.Quotient.mk (I i) r = g i :=
      (Ideal.Quotient.mk_surjective <| g .)
    have ⟨(f : ι → R), (_ : ∀ i, Ideal.Quotient.mk (I i) (f i) = g i)⟩ :=
      -- TODO: Weaken to finite Choice because this is a bit of an eyesore.
      Classical.axiomOfChoice this
    sorry

end CRT

end Ring
