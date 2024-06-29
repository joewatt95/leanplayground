import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

import Leanplayground.MathInLean.Utils.Tactic

namespace NumberTheory

theorem exists_prime_factor {n : ℕ}
  (_ : 2 ≤ n)
  : ∃ p, p.Prime ∧ p ∣ n :=
  suffices ¬ n.Prime → ∃ p, p.Prime ∧ p ∣ n  by tauto
  λ _ : ¬ n.Prime ↦
    have : ∃ m < n, m ∣ n ∧ m ≠ 1 := by
      duper [*, Nat.prime_def_lt] {portfolioInstance := 1}
    have ⟨m, (_ : m < n), (_ : m ∣ n), (_ : m ≠ 1)⟩ := this

    have : 2 ≤ m :=
      have : m ≠ 0 := by aesop
      by omega

    have ⟨p, (_ : p.Prime), (_ : p ∣ m)⟩ := exists_prime_factor this
    have := calc
      p ∣ m := ‹_›
      _ ∣ n := ‹_›
    by tauto

theorem primes_infinite {n : ℕ}
  : ∃ p > n, p.Prime :=
  -- open scoped ! factorial notation
  open scoped Nat in

  have : 2 ≤ (n + 1)! + 1 :=
    have : 2 ≤ n ! + 1 := have := n.factorial_pos; by omega
    have : n ! ≤ (n + 1)! := Nat.factorial_le <| by omega
    by omega

  have ⟨p, (_ : p.Prime), (_ : p ∣ (n + 1)! + 1)⟩ := exists_prime_factor this

  suffices p > n by tauto
  suffices ¬ p ≤ n by aesop
  λ _ ↦
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
      duper [*, Finset.single_le_prod', Nat.Prime.one_le, Nat.prime_two]
        {portfolioInstance := 1}

    have ⟨p, (_ : p.Prime), (_ : p ∣ S_primes_prod + 1)⟩ :=
      exists_prime_factor <| Nat.le_succ_of_le this

    have : p ∣ S_primes_prod := by
      duper [*, dvd_prod_of_mem] {portfolioInstance := 1}
    have : p ∣ 1 := by duper [*, Nat.dvd_add_right] {portfolioInstance := 1}
    show ⊥ by aesop

private lemma mod_4_eq_3_or {m n : ℕ}
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

private lemma exists_prime_factor_mod_4_eq_3 {n : ℕ}
  (_ : n % 4 = 3)
  : ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 :=
  let φ := ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3
  suffices ¬ n.Prime → φ by tauto
  λ _ ↦
    have ⟨m, _, _, _⟩ : ∃ m < n, m ∣ n ∧ m ≠ 1 :=
      suffices 2 ≤ n by duper [*, Nat.prime_def_lt] {portfolioInstance := 1}
      by omega

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
      -- This is needed to justify the following well-founded recursion on n / m.
      have : n / m < n :=
        suffices 0 < n ∧ 1 < m from And.elim Nat.div_lt_self this
        have : n % 4 = 3 ∧ m ∣ n ∧ m ≠ 1 := by tauto
        have : m ≠ 0 := λ _ ↦ show ⊥ by aesop
        by omega

      have ⟨p, (_ : p.Prime), (_ : p ∣ n / m), (_ : p % 4 = 3)⟩ :=
        exists_prime_factor_mod_4_eq_3 ‹n / m % 4 = 3›
      have := calc
        p ∣ n / m := ‹_›
        _ ∣ n     := Nat.div_dvd_of_dvd ‹_›
      show φ by tauto

-- set_option trace.profiler true
theorem primes_mod_4_eq_3_infinite {n : ℕ}
  : ∃ p > n, p.Prime ∧ p % 4 = 3 :=
  -- set_option trace.profiler true in
  suffices ¬ ∀ p > n, p.Prime → p % 4 ≠ 3 by aesop
  λ _ ↦
    let S := {p | p.Prime ∧ p % 4 = 3}

    have : BddAbove S :=
      suffices ∀ p ∈ S, p ≤ n from ⟨n, this⟩
      λ p (_ : p ∈ S) ↦
        have : ¬ p > n := λ _ ↦ show ⊥ by aesop
        show p ≤ n by omega

    have : S.Finite := Set.finite_iff_bddAbove.mpr this
    let S : Finset ℕ := this.toFinset

    let S_prod := ∏ m in S.erase 3, m

    have : (4 * S_prod + 3) % 4 = 3 := by omega
    have ⟨p, (_ : p.Prime), (_ : p ∣ 4 * S_prod + 3), (_ : p % 4 = 3)⟩ :=
      exists_prime_factor_mod_4_eq_3 this

    suffices p ≠ 3 ∧ p = 3 from And.elim (. <| .) this

    have : p ≠ 3 :=
      λ _ ↦
        have : 3 ∣ 4 * S_prod ∧ ¬ 3 ∣ 4 := ⟨by aesop, by decide⟩
        have : 3 ∣ S_prod := by
          duper [this, Nat.prime_three, Nat.Prime.dvd_mul]
            {portfolioInstance := 1}

        have ⟨p', _, _⟩ : ∃ p' ∈ S.erase 3, 3 ∣ p' := by
          refine Prime.exists_mem_finset_dvd ?_ this
          duper [Nat.prime_iff, Nat.prime_three] {portfolioInstance := 1}
          -- duper
          --   [this, Prime.exists_mem_finset_dvd, Nat.prime_iff, Nat.prime_three]
          --   {portfolioInstance := 1}

        have : p'.Prime ∧ p' ≠ 3 ∧ 3 ∣ p' := by aesop
        show ⊥ by duper [this, Nat.prime_def_lt''] {portfolioInstance := 3}

    have : p = 3 :=
      have : p ∈ S.erase 3 := by aesop

      have := calc
        p ∣ S_prod     := dvd_prod_of_mem _ this
        _ ∣ 4 * S_prod := by aesop

      have : p ∣ 3 := by
        duper [this, ‹p ∣ 4 * S_prod + 3›, Nat.dvd_add_iff_right]
          {portfolioInstance := 1}

      show p = 3 by
        duper [this, ‹p.Prime›, Nat.prime_dvd_prime_iff_eq, Nat.prime_three]
          {portfolioInstance := 1}

    ⟨‹p ≠ 3›, ‹p = 3›⟩

end NumberTheory
