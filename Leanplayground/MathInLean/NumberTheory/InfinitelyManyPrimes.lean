import Mathlib.Tactic
import Leanplayground.MathInLean.Utils.Tactics

namespace NumberTheory

theorem exists_prime_factor {n : ℕ} (_ : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n :=
  match em _ with
  | .inl (_ : n.Prime) => by aesop
  | .inr (_ : ¬ n.Prime) =>
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 := by duper [Nat.prime_def_lt, *]
    let ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : m ≠ 0 := by aesop
    have : 2 ≤ m := by omega

    let ⟨p, (_ : p.Prime), (_ : p ∣ m)⟩ := exists_prime_factor ‹2 ≤ m›
    have := calc
      p ∣ m := by assumption
      _ ∣ n := by assumption

    by aesop

theorem primes_infinite : ∀ n, ∃ p > n, (p : ℕ).Prime
  | n =>
    -- open Scoped ! factorial notation
    open scoped Nat in

    have :=
      have : 0 < n ! := n.factorial_pos
      have : n ! ≤ (n + 1)! := Nat.factorial_le <| by aesop
      calc
        2 ≤ n ! + 1      := by aesop
        _ ≤ (n + 1)! + 1 := by aesop

    let ⟨p, (_ : p.Prime), (_ : p ∣ (n + 1)! + 1)⟩ := exists_prime_factor this

    suffices ¬ p ≤ n by aesop
    λ _ : p ≤ n ↦
      have : p ∣ (n + 1)! :=
        suffices 0 < p ∧ p ≤ n + 1 by duper [Nat.dvd_factorial, *]
        have : 2 ≤ p := by duper [Nat.prime_def_lt, ‹p.Prime›]
        by omega

      have : p ∣ 1 := by duper [Nat.dvd_add_right, *]
      show ⊥ by aesop

end NumberTheory
