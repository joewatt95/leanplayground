import Mathlib.Tactic
import Leanplayground.MathInLean.Utils.Tactic

namespace NumberTheory

theorem exists_prime_factor {n : ℕ} (_ : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n :=
  match em _ with
  | .inl (_ : n.Prime) => by tauto
  | .inr (_ : ¬ n.Prime) =>
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 := by duper [*, Nat.prime_def_lt] {portfolioInstance := 1}
    let ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : m ≠ 0 := by aesop
    have : 2 ≤ m := by omega

    let ⟨p, (_ : p.Prime), (_ : p ∣ m)⟩ := exists_prime_factor this
    have := calc
      p ∣ m := by assumption
      _ ∣ n := by assumption

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

end NumberTheory
