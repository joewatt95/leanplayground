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

#check Ideal.quotientInfToPiQuotient

-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
-- Remainder Theorem.
def crtMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i where
  toFun := sorry

  map_one' := sorry

  map_mul' := sorry

  map_zero' := sorry

  map_add' := sorry

end CRT

end Ring
