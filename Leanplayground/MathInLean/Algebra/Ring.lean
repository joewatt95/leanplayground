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

-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
-- Remainder Theorem.
def crtMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
  -- Pi.ringHom allows us to use the universal property of Pi types to construct
  -- a ring morphism into a Pi type.
  let f_i : ∀ i, R →+* R ⧸ I i := (Ideal.Quotient.mk <| I .)
  let f : R →+* ∀ i, R ⧸ I i := Pi.ringHom f_i

  have : RingHom.ker f = ⨅ i, I i := Ideal.ker_Pi_Quotient_mk _

  -- Lift the morphism to the quotient ring via the corresponding universal
  -- property.
  let f' : R ⧸ RingHom.ker f →+* ∀ i, R ⧸ I i := f.kerLift

  -- The following line uses Curry-Howard to change the type of `f'`:
  -- 1. We view f' as a proof (ie term) of the proposition (ie type)
  --    `R ⧸ RingHom.ker f →+* ∀ i, R ⧸ I i`
  -- 2. We then use `rwa` to do the following:
  --    2a. It rewrites at f' using the equation `RingHom.ker f = ⨅ i, I i`, so
  --        that `f'` is now a proof (ie term) of the proposition (ie type)
  --        `(R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i`
  --    2b. It uses `assumption` to supply `f'` as a proof (ie term) of the goal
  --    proposition (ie desired type of the output)
  show (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i by rwa [this] at f'

-- def crtMap' (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* ∀ i, R ⧸ I i :=
--   Ideal.quotientInfToPiQuotient _

private lemma crtMap_mk {I : ι → Ideal R} {x : R} :
  crtMap I ⟦x⟧ = λ i ↦ Ideal.Quotient.mk (I i) x := by
  simp [crtMap]
  sorry

private lemma crtMap_mk' {I : ι → Ideal R} {x : R} {i : ι} :
  crtMap I ⟦x⟧ i = Ideal.Quotient.mk (I i) x := by
  simp [crtMap]
  sorry

end CRT

end Ring
