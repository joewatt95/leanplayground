-- import Mathlib.RingTheory.Ideal.Quotient
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
-- #check Ideal.ker_Pi_Quotient_mk

-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the
-- Chinese Remainder Theorem.
def crtMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  -- Pi.ringHom allows us to use the universal property of Pi types to construct
  -- a ring morphism into a Pi type.
  let f_i : ∀ i, R →+* R ⧸ I i := (Ideal.Quotient.mk <| I .)
  let f : R →+* ∀ i, R ⧸ I i := Pi.ringHom f_i

  -- Lift the morphism to the quotient ring via the corresponding universal
  -- property.
  let f' : R ⧸ RingHom.ker f →+* ∀ i, R ⧸ I i := f.kerLift

  have : RingHom.ker f = ⨅ i, I i := Ideal.ker_Pi_Quotient_mk _
  this ▸ f'

-- def crtMap' (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
--   Ideal.quotientInfToPiQuotient _

-- set_option pp.proofs true

-- #print crtMap

-- #check cast_eq

private lemma crtMap_mk {I : ι → Ideal R} {r : R} :
  crtMap I ⟦r⟧ = λ i ↦ (⟦r⟧ : R ⧸ I i):= by
  simp [crtMap]
  sorry

private lemma crtMap_mk' {I : ι → Ideal R} {r : R} {i : ι} :
  crtMap I ⟦r⟧ i = (⟦r⟧ : R ⧸ I i) := by
  simp [crtMap]
  sorry

end CRT

end Ring
