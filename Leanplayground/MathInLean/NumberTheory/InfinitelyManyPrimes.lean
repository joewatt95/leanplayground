-- import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

import Leanplayground.MathInLean.Utils.Tactic

namespace NumberTheory

theorem exists_prime_factor {n : ℕ}
  (_ : 2 ≤ n)
  : ∃ p, p.Prime ∧ p ∣ n :=
  suffices ¬ n.Prime → ∃ p, p.Prime ∧ p ∣ n  by tauto
  λ _ : ¬ n.Prime ↦
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 := by duper [*, Nat.prime_def_lt] {portfolioInstance := 1}
    have ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : 2 ≤ m :=
      have : m ≠ 0 := by aesop
      by omega

    let ⟨p, (_ : p.Prime), (_ : p ∣ m)⟩ := exists_prime_factor this
    have := calc
      p ∣ m := ‹_›
      _ ∣ n := ‹_›
    by tauto

theorem primes_infinite {n : ℕ}
  : ∃ p > n, p.Prime :=
  -- open Scoped ! factorial notation
  open scoped Nat in

  have : 2 ≤ (n + 1)! + 1 :=
    have : 2 ≤ n ! + 1 := have := n.factorial_pos; by omega
    have : n ! ≤ (n + 1) ! := by apply Nat.factorial_le; omega
    by omega

  have ⟨p, (_ : p.Prime), (_ : p ∣ (n + 1)! + 1)⟩ := exists_prime_factor this

  suffices p > n by tauto
  suffices ¬ p ≤ n by aesop
  λ _ : p ≤ n ↦
    have := calc
      p ∣ n !      := by duper [*, Nat.Prime.dvd_factorial] {portfolioInstance := 1}
      _ ∣ (n + 1)! := by simp only [Nat.factorial_succ, dvd_mul_left]
    have : p ∣ 1 := by duper [*, Nat.dvd_add_right] {portfolioInstance := 1}
    show ⊥ by aesop

open BigOperators Finset

theorem primes_infinite' {S : Finset ℕ}
  : ∃ p, p.Prime ∧ p ∉ S :=
  let S_primes := S.filter Nat.Prime
  suffices ¬ ∀ {p}, p.Prime ↔ p ∈ S_primes by aesop
  λ _ ↦
    let S_primes_prod := ∏ n ∈ S_primes, n

    have : 2 ≤ S_primes_prod := by
      duper [*, Finset.single_le_prod', Nat.Prime.one_le, Nat.prime_two] {portfolioInstance := 1}

    have ⟨p, (_ : p.Prime), (_ : p ∣ S_primes_prod + 1)⟩ :=
      exists_prime_factor <| Nat.le_succ_of_le this

    have : p ∣ S_primes_prod := by duper [*, dvd_prod_of_mem] {portfolioInstance := 1}
    have : p ∣ 1 := by duper [*, Nat.dvd_add_right] {portfolioInstance := 1}
    show ⊥ by aesop

lemma mod_4_eq_3_or {m n : ℕ}
  (_ : m * n % 4 = 3)
  : m % 4 = 3 ∨ n % 4 = 3 :=
  have : (m % 4) * (n % 4) % 4 = 3 := by
    duper [*, Nat.mul_mod] {portfolioInstance := 1}
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
  let φ := ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3
  suffices ¬ n.Prime → φ by tauto
  λ _ : ¬ n.Prime ↦
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 :=
      suffices 2 ≤ n by duper [*, Nat.prime_def_lt] {portfolioInstance := 1}
      by omega

    have ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : m % 4 = 3 ∨ n / m % 4 = 3 := by
      duper [*, Nat.mul_div_cancel', mod_4_eq_3_or] {portfolioInstance := 1}

    match this with
    | .inl (_ : m % 4 = 3) =>
      have ⟨p, (_ : p.Prime), (_ : p ∣ m), (_ : p % 4 = 3)⟩ :=
        exists_prime_factor_mod_4_eq_3 ‹m % 4 = 3›
      have := calc
        p ∣ m := ‹_›
        _ ∣ n := ‹_›
      show φ by tauto

    | .inr (_ : n / m % 4 = 3) =>
      -- This is required to justify the well-founded recursion on n / m.
      have : n / m < n :=
        suffices 0 < n ∧ 1 < m by
          duper [*, Nat.div_lt_self] {portfolioInstance := 1}
        have : n % 4 = 3 ∧ m ∣ n ∧ m ≠ 1 := by tauto
        suffices m ≠ 0 by omega
        by aesop

      have ⟨p, (_ : p.Prime), (_ : p ∣ n / m), (_ : p % 4 = 3)⟩ :=
        exists_prime_factor_mod_4_eq_3 ‹n / m % 4 = 3›
      have := calc
        p ∣ n / m := ‹_›
        _ ∣ n     := Nat.div_dvd_of_dvd ‹_›
      show φ by tauto

theorem primes_mod_4_eq_3_infinite {n : ℕ}
  : ∃ p > n, p.Prime ∧ p % 4 = 3 :=
  suffices ¬ ∀ p > n, p.Prime → p % 4 ≠ 3 by aesop
  λ _ ↦
    let S := {p | p.Prime ∧ p % 4 = 3}
    have : ∀ p ∈ S, p ≤ n
      | p, (_ : p ∈ S) =>
        have : ¬ p > n := λ _ ↦ by aesop
        by omega

    let S : Finset ℕ :=
      have : BddAbove S := ⟨n, this⟩
      have : S.Finite := by
        duper [*, Set.finite_iff_bddAbove] {portfolioInstance := 1}
      this.toFinset

    let S_prod := ∏ m in S.erase 3, m

    have : (4 * S_prod + 3) % 4 = 3 := by omega
    have ⟨p, (_ : p.Prime), (_ : p ∣ 4 * S_prod + 3), (_ : p % 4 = 3)⟩ :=
      exists_prime_factor_mod_4_eq_3 this

    have : p ≠ 3
      | (_ : p = 3) =>
        have : 3 ∣ 4 * S_prod := by aesop
        have : 3 ∣ S_prod :=
          have {a b} : ¬ 3 ∣ 4 ∧ (3 ∣ a * b ↔ 3 ∣ a ∨ 3 ∣ b) :=
            ⟨by omega, Nat.prime_three.dvd_mul⟩
          by aesop

        have ⟨p', _, _⟩ : ∃ p' ∈ S.erase 3, 3 ∣ p' := by
          refine (Prime.dvd_finset_prod_iff ?_ id).mp this
          duper [Nat.prime_iff, Nat.prime_three]

        have : p'.Prime ∧ p' ≠ 3 ∧ 3 ∣ p' := by aesop
        show ⊥ by duper [Nat.prime_def_lt'', this] {portfolioInstance := 3}

    have := calc
      p ∣ S_prod     := dvd_prod_of_mem id <| show p ∈ S.erase 3 by aesop
      _ ∣ 4 * S_prod := by aesop

    have : p ∣ 3 := Nat.dvd_add_iff_right this |>.mpr ‹_›
    have : p = 3 := by
      duper [Nat.prime_dvd_prime_iff_eq, Nat.prime_three, ‹p.Prime›, this]
        {portfolioInstance := 1}

    show ⊥ from ‹p ≠ 3› ‹p = 3›

end NumberTheory
