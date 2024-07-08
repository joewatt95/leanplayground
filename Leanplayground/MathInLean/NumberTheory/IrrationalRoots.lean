import Mathlib.Data.Nat.Factorization.Basic
import Leanplayground.MathInLean.Utils.Tactic

namespace NumberTheory

lemma even_iff_even_sqr {m : ℕ} : 2 ∣ m ^ 2 ↔ 2 ∣ m := by
  duper [pow_two, Nat.prime_two, Nat.Prime.dvd_mul]

example {m n : ℕ} (_ : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2
  | (_ : m ^ 2 = 2 * n ^ 2) =>
  have : 2 ∣ m := by rw [←even_iff_even_sqr]; omega
  have ⟨k, (_ : m = 2 * k)⟩ := this

  have := calc
    2 * n ^ 2 = (2 * k) ^ 2 := by aesop
            _ = 4 * k ^ 2   := by ring

  have : 2 ∣ n := by rw [←even_iff_even_sqr]; omega

  show ⊥ by duper [*, Nat.dvd_gcd] {portfolioInstance := 7}

-- #check Nat.factors
-- #check Nat.prime_of_mem_factors
-- #check Nat.prod_factors
-- #check Nat.factors_unique

example {m n k r p : ℕ}
  (_ : n ≠ 0) (_ : m ^ k = r * n ^ k)
  : k ∣ r.factorization p :=
  match em _ with
  | .inl (_ : r = 0) => by aesop
  | .inr (_ : r ≠ 0) =>
    have := calc
          k * m.factorization p
      _ = (m ^ k).factorization p                   := by simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      _ = (r * n ^ k).factorization p               := by aesop
      _ = r.factorization p + k * n.factorization p := by aesop

    have := calc
          r.factorization p
      _ = k * m.factorization p - k * n.factorization p := by aesop
      _ = k * (m.factorization p - n.factorization p)   := by rw [Nat.mul_sub_left_distrib]

    show k ∣ r.factorization p by aesop

end NumberTheory
