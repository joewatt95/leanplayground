import Mathlib
import Leanplayground.MathInLean.Utils.Tactic

namespace VectorSpaces

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)
  (H : Submodule K W)
  : Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by simp_all
  add_mem' := by aesop
  smul_mem' := by aesop

end VectorSpaces
