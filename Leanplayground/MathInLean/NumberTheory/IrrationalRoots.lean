import Mathlib.Data.Nat.Factorization.Basic

import Leanplayground.MathInLean.Utils.Tactic

namespace NumberTheory

lemma even_iff_even_sqr {m : ℕ} : 2 ∣ m ^ 2 ↔ 2 ∣ m := by
  duper [pow_two, Nat.prime_two, Nat.Prime.dvd_mul] {portfolioInstance := 1}

example {m n : ℕ} (_ : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 :=
  λ _ ↦
    have : 2 ∣ m ^ 2 := by omega
    have : 2 ∣ m := even_iff_even_sqr.mp this
    have ⟨k, (_ : m = 2 * k)⟩ := this

    have := calc
      2 * n ^ 2 = (2 * k) ^ 2 := by egg [*]
              _ = 4 * k ^ 2   := by ring

    have : 2 ∣ n ^ 2 := by omega
    have : 2 ∣ n := even_iff_even_sqr.mp this

    show ⊥ by duper [*, Nat.dvd_gcd] {portfolioInstance := 7}

-- #check Nat.factors
-- #check Nat.prime_of_mem_factors
-- #check Nat.prod_factors
-- #check Nat.factors_unique

example {m n k r p : ℕ}
  (_ : n ≠ 0) (_ : m ^ k = r * n ^ k)
  : k ∣ r.factorization p :=
  match em _ with
  | .inl (_ : r = 0) => by simp_all only
    [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, dvd_zero]
  | .inr (_ : r ≠ 0) =>
    have := calc
          k * m.factorization p
      _ = (m ^ k).factorization p                   := by simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      _ = (r * n ^ k).factorization p               := by simp_all only [Nat.factorization_pow]
      _ = r.factorization p + k * n.factorization p := by simp_all

    have := calc
          r.factorization p
      _ = k * m.factorization p - k * n.factorization p := by  simp_all only [add_tsub_cancel_right]
      _ = k * (m.factorization p - n.factorization p)   := by rw [Nat.mul_sub_left_distrib]

    show k ∣ r.factorization p by  simp_all only [dvd_mul_right]

end NumberTheory
