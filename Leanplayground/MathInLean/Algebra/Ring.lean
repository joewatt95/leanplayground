import Mathlib.RingTheory.Ideal.QuotientOperations

import Leanplayground.MathInLean.Utils.Tactic

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
theorem add_Inf_of_forall_add {s : Finset ι}
  (_ : ∀ j ∈ s, I + J j = ⊤)
  : I + ⨅ j ∈ s, J j = ⊤ :=
  -- set_option trace.profiler true in
  suffices ⊤ ≤ I + ⨅ j ∈ s, J j by
    simp_all only [Submodule.add_eq_sup, top_le_iff]

  match s.eq_empty_or_nonempty with
  | .inl (_ : s = ∅) => by simp [‹s = ∅›]
  | .inr ⟨i, (_ : i ∈ s)⟩ =>
    have : I + J i = ⊤ := ‹∀ j ∈ s, I + J j = ⊤› _ ‹_›

    let s' := s.erase i
    let K := ⨅ j ∈ s', J j

    -- Well-founded recusion on s', via the ordering induced by finset cardinality.
    have : I + K = ⊤ :=
      have : s'.card < s.card := Finset.card_erase_lt_of_mem ‹i ∈ s›
      have : ∀ j ∈ s', I + J j = ⊤ := by simp_all [s']
      add_Inf_of_forall_add this

    have : ⨅ j ∈ s, J j = K ⊓ J i :=
      have : ⨅ j ∈ insert i s', J j = J i ⊓ K := Finset.iInf_insert _ _ _
      have : s = insert i (s.erase i) := by
        simp_all only [Submodule.add_eq_sup, Finset.insert_erase]
      by rwa [inf_comm, this]

    calc
      ⊤ = I + K                 := Eq.symm ‹_›
      _ = I + K * (I + J i)     := by simp [‹I + J i = ⊤›]
      _ = (I + K * I) + K * J i := by ring
      _ = I + K * J i           := by simp_all only [Submodule.add_eq_sup, Ideal.sup_mul_left_self]
      _ ≤ I + K ⊓ J i           := by gcongr; exact Ideal.mul_le_inf
      _ = I + ⨅ j ∈ s, J j      := by rw [this]

termination_by s.card

theorem isCoprime_Inf {s : Finset ι}
  : (∀ j ∈ s, IsCoprime I <| J j) → IsCoprime I (⨅ j ∈ s, J j) := by
  simp only [Ideal.isCoprime_iff_add, Submodule.add_eq_sup, Ideal.one_eq_top]
  exact add_Inf_of_forall_add

end

end CRT

end Ring
