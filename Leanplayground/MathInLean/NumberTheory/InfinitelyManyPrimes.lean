import Mathlib.Tactic
import Leanplayground.MathInLean.Utils.Tactic

namespace NumberTheory

theorem exists_prime_factor {n : ℕ} (_ : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n :=
  suffices ¬ n.Prime → ∃ p, p.Prime ∧ p ∣ n  by tauto
  λ _ : ¬ n.Prime ↦
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 := by duper [*, Nat.prime_def_lt] {portfolioInstance := 1}
    let ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : 2 ≤ m :=
      have : m ≠ 0 := by aesop
      by omega

    let ⟨p, (_ : p.Prime), (_ : p ∣ m)⟩ := exists_prime_factor this
    have := calc
      p ∣ m := ‹_›
      _ ∣ n := ‹_›

    by tauto

theorem primes_infinite : ∀ {n : ℕ}, ∃ p > n, p.Prime
  | n =>
    -- open Scoped ! factorial notation
    open scoped Nat in

    have : 2 ≤ (n + 1)! + 1 :=
      have : 2 ≤ n ! + 1 := have := n.factorial_pos; by omega
      have : n ! ≤ (n + 1) ! := by apply Nat.factorial_le; omega
      by omega

    let ⟨p, (_ : p.Prime), (_ : p ∣ (n + 1)! + 1)⟩ := exists_prime_factor this

    suffices ¬ p ≤ n by aesop
    λ _ : p ≤ n ↦
      have := calc
        p ∣ n !      := by duper [*, Nat.Prime.dvd_factorial] {portfolioInstance := 1}
        _ ∣ (n + 1)! := by simp only [Nat.factorial_succ, dvd_mul_left]
      have : p ∣ 1 := by duper [*, Nat.dvd_add_right] {portfolioInstance := 1}
      show ⊥ by aesop

open BigOperators Finset

theorem primes_infinite' : ∀ {S : Finset ℕ}, ∃ p, p.Prime ∧ p ∉ S
  | S =>
    let S_primes := S.filter Nat.Prime
    suffices ¬ ∀ {p}, p.Prime ↔ p ∈ S_primes by aesop
    λ _ ↦
      let S_primes_prod := ∏ n ∈ S_primes, n

      have : 2 ≤ S_primes_prod := by
        duper [*, Finset.single_le_prod', Nat.Prime.one_le, Nat.prime_two] {portfolioInstance := 1}

      let ⟨p, (_ : p.Prime), (_ : p ∣ S_primes_prod + 1)⟩ :=
        exists_prime_factor <| Nat.le_succ_of_le this

      have : p ∣ S_primes_prod := by duper [*, dvd_prod_of_mem] {portfolioInstance := 1}
      have : p ∣ 1 := by duper [*, Nat.dvd_add_right] {portfolioInstance := 1}
      show ⊥ by aesop

lemma mod_4_eq_3_or {m n : ℕ} (_ : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 :=
  have : (m % 4) * (n % 4) % 4 = 3 := by duper [*, Nat.mul_mod] {portfolioInstance := 1}
  have : m % 4 ≠ 0 ∧ n % 4 ≠ 0 := ⟨λ _ ↦ by aesop, λ _ ↦ by aesop⟩

  suffices ¬ ((m % 4 = 1 ∨ m % 4 = 2) ∧ (n % 4 = 1 ∨ n % 4 = 2)) by omega
  (by rcases . with ⟨_ | _, _ | _⟩; all_goals simp_all)

-- lemma aux {m n : ℕ}
--   (_ : m ∣ n) (_ : 2 ≤ m) (_ : m < n)
--   : n / m ∣ n ∧ n / m < n :=
--   suffices 0 < n ∧ 1 < m by duper [*, Nat.div_dvd_of_dvd, Nat.div_lt_self]
--   by omega

theorem exists_prime_factor_mod_4_eq_3 {n : ℕ}
  (_ : n % 4 = 3)
  : ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 :=
  suffices ¬ n.Prime → ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 by tauto
  λ _ : ¬ n.Prime ↦
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 :=
      have : 2 ≤ n := by omega
      by duper [*, Nat.prime_def_lt] {portfolioInstance := 1}

    let ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : m % 4 = 3 ∨ n / m % 4 = 3 := by
      duper [*, Nat.mul_div_cancel', mod_4_eq_3_or] {portfolioInstance := 1}

    match this with
    | .inl (_ : m % 4 = 3) =>
      let ⟨p, (_ : p.Prime), (_ : p ∣ m), (_ : p % 4 = 3)⟩ :=
        exists_prime_factor_mod_4_eq_3 ‹m % 4 = 3›
      have := calc
        p ∣ m := ‹_›
        _ ∣ n := ‹_›
      by tauto

    | .inr (_ : n / m % 4 = 3) =>
      -- This is required to justify the well-founded recursion on n / m.
      have : n / m < n :=
        suffices m ≠ 0 by apply Nat.div_lt_self; all_goals omega
        λ _ : m = 0 ↦ nomatch calc
          3 = n / m % 4 := Eq.symm ‹_›
          _ = n / 0 % 4 := by rw [‹m = 0›]
          _ = 0         := by simp only [Nat.div_zero, Nat.zero_mod]

      let ⟨p, (_ : p.Prime), (_ : p ∣ n / m), (_ : p % 4 = 3)⟩ :=
        exists_prime_factor_mod_4_eq_3 ‹n / m % 4 = 3›
      have := calc
        p ∣ n / m := by assumption
        _ ∣ n     := Nat.div_dvd_of_dvd ‹_›
      by tauto

end NumberTheory
