-- import LeanCopilot

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

import Std.Data.List.Lemmas

namespace MyNat

inductive Leq : (m n : ℕ) → Prop
| Self : Leq m m
| Succ (m_leq_n : Leq m n) : Leq m (n + 1)

infix:50 " leq " => Leq

lemma zero_leq : ∀ {m}, 0 leq m
| 0 => .Self
| m + 1 =>
  have : 0 leq m := zero_leq
  show 0 leq m + 1 from this.Succ

macro m:term "leq'" n:term : term => `(∃ d : ℕ, $m + d = $n)

private lemma eq_zero_or_succ : ∀ {n}, n = 0 ∨ ∃ m, n = m + 1
| 0 => .inl rfl
| n + 1 =>
  suffices ∃ m, n + 1 = m + 1 from .inr this

  match (eq_zero_or_succ : n = 0 ∨ ∃ m, n = m + 1) with
  | .inl n_eq_zero =>
    show ∃ m, n + 1 = m + 1 from ⟨0, by rw [n_eq_zero]⟩

  | .inr ⟨m, n_eq_m_succ⟩ =>
    show ∃ m, n + 1 = m + 1 from ⟨m + 1, by rw [n_eq_m_succ]⟩

private lemma leq'_of_leq : ∀ {n}, m leq n → m leq' n
| _, (.Self : m leq m) =>
  show ∃ d, m + d = m from ⟨0, rfl⟩
| .(_ + 1), (.Succ m_leq_n) =>
  have : m leq' _ := leq'_of_leq m_leq_n
  let ⟨d, h⟩ := this
  have : m + (d + 1) = _ + 1 := by rw [←h]; ring
  show ∃ d, m + d = _ + 1 from ⟨d + 1, this⟩

private lemma leq_of_leq' : ∀ {n}, (∃ d, m + d = n) → m leq n
| n, ⟨0, h⟩ =>
  have : m = n := by simp only [add_zero] at h ; exact h
  show m leq n by rw [this]; exact Leq.Self

| n + 1, ⟨d + 1, h⟩ =>
  have : (m + d) + 1 = n + 1 := by rw [add_assoc, h]
  have : ∃ d, m + d = n := ⟨d, by simp only [add_left_inj] at this ; assumption⟩
  have : m leq n := leq_of_leq' this
  show m leq n + 1 from this.Succ

@[simp]
theorem leq_iff_leq' : (m leq n) ↔ m leq' n :=
  ⟨leq'_of_leq, leq_of_leq'⟩

private lemma Leq.reflexive : x leq x := Leq.Self

private lemma Leq.transitive : (x leq y) → (y leq z) → x leq z
| x_leq_y, y_leq_z =>
  have ⟨d1, h1⟩ : ∃ d1, x + d1 = y :=
    by simp only [leq_iff_leq'] at x_leq_y ; assumption
  have ⟨d2, h2⟩ : ∃ d2, y + d2 = z :=
    by simp only [leq_iff_leq'] at y_leq_z ; assumption
  have : ∃ d, x + d = z := ⟨d1 + d2, by ring_nf; rw [h1, h2]⟩
  show x leq z by rw [←leq_iff_leq'] at this; assumption

instance : Trans Leq Leq Leq := ⟨Leq.transitive⟩

private lemma Leq.antisymmetric : x leq y → y leq x → x = y
| x_leq_y, y_leq_x =>
  have ⟨d1, h1⟩ : ∃ d1, x + d1 = y :=
    by simp only [leq_iff_leq'] at x_leq_y ; assumption
  have ⟨d2, h2⟩ : ∃ d2, y + d2 = x :=
    by simp only [leq_iff_leq'] at y_leq_x ; assumption
  have : x + (d1 + d2) = x := by rw [←h1] at h2; ring_nf; assumption
  have : d1 + d2 = 0 := Nat.add_left_cancel this
  have : d1 = 0 :=
    match (eq_zero_or_succ : d1 = 0 ∨ ∃ d, d1 = d + 1) with
    | .inl d1_eq_zero => d1_eq_zero
    | .inr ⟨d, d1_eq_d_succ⟩ =>
      suffices ⊥ from this.elim
      have : d + d2 + 1 = 0 := by
        ring_nf
        simp only
          [d1_eq_d_succ, add_eq_zero, one_ne_zero, and_false, false_and]
          at this
      show ⊥ from Nat.succ_ne_zero _ this
  show x = y by rw [this] at h1; exact h1

private lemma leq_plus : ∀ {b}, a leq a + b
| 0 => .Self
| b + 1 => calc
  a leq a + b     := leq_plus
  _ leq a + b + 1 := by simp only [leq_iff_leq', add_right_inj, exists_eq]

private lemma eq_zero_of_leq : ∀ {n}, n leq 0 → n = 0
| 0, _ => rfl

private lemma leq_plus_of_leq : a leq b → c leq d → a + c leq b + d
| .Self, .Self => .Self

| .Self, .Succ c_leq => calc
  a + c leq a + _ := by exact leq_plus_of_leq .Self c_leq
      _ leq a + _ + 1 := .Succ .Self

| .Succ a_leq, .Self => calc
  a + c leq _ + c := by exact leq_plus_of_leq a_leq .Self
      _ leq _ + c + 1 := .Succ .Self
      _ = _ + 1 + c := by ring_nf

| .Succ a_leq, .Succ c_leq => calc
  a + c leq _ + _ := by exact leq_plus_of_leq a_leq c_leq
      _ leq _ + _ + 2 := leq_plus
      _ = _ + 1 + _ + 1 := by
        simp only [Nat.add_eq, add_zero, Nat.succ.injEq]
        ring_nf

private lemma h :
  ∀ {as bs : List α},
    (∀ (i : Fin as.length), ∃ j : Fin bs.length, i.val = j) →
    as.length ≤ bs.length

| [], _, _ | a :: as, [], _ => by aesop
| a :: as, b :: bs, h =>
  suffices as.length ≤ bs.length from sorry
  suffices ∀ (i : Fin as.length), ∃ j : Fin bs.length, i.val = j from sorry
  λ ⟨i, h_i⟩ ↦
    have : as.length < (a :: as).length := by aesop
    let i' : Fin (a :: as).length := ⟨i, by omega⟩
    have := h i'
    sorry
    -- ⟨⟨i.pred, sorry⟩, sorry⟩

private lemma leq_sum_of_leq :
∀ {as bs : List ℕ},
  (∀ i, ∃ j, i.val = j.val ∧ as.get i ≤ bs.get j) →
  as.length ≤ bs.length ∧ as.sum ≤ bs.sum

| [], _, _ | a :: as, [], h => by aesop

| a :: as, b :: bs, h =>
  -- have : as.length ≤ bs.length := by aesop
  have : as.length < (a :: as).length := by aesop
  have : ∀ i, ∃ j, i.val = j.val ∧ as.get i ≤ bs.get j
    | ⟨i, _⟩ =>
      let ⟨⟨i, h_i⟩, _, h⟩ := h ⟨i, by omega⟩
      match i with
      | 0 => sorry
      | i + 1 =>
        ⟨⟨i.pred, sorry⟩, sorry, sorry⟩
  sorry

  -- have : as.length = bs.length := by aesop
  -- have := calc
  --   as.length + 1 = (a :: as).length := by aesop
  --               _ = (b :: bs).length := by aesop
  --               _ = bs.length + 1 := by aesop
  -- sorry

--   have h_len : as.length = bs.length := by aesop
--   have :
--     ∀ i (_ : i.val < as.length),
--       as.get i ≤ bs.get ⟨i.val, by linarith⟩ :=
--     λ i h' ↦
--       have := calc
--         i.val < as.length := by exact h'
--         _ < (a :: as).length := by aesop
--       have := h ⟨i.val, by aesop⟩ this
--       sorry
--   sorry

-- | a :: as, b :: bs, h =>
--   suffices as.sum leq bs.sum from sorry
--   have : ∀ i, ∃ j, j.val = i.val ∧ as.get i leq bs.get j := by aesop
--   sorry

private lemma leq_plus_of_leq' : a leq b → a + c leq b + c :=
  (leq_plus_of_leq . .Self)

-- private lemma leq_plus_of_leq : ∀ {x y z}, x leq y → x + z leq y + z
-- | _, _, 0, x_leq_y => x_leq_y
-- | x, y, z + 1, x_leq_y =>
--   have : x + z leq y + z := leq_plus_of_leq x_leq_y
--   have ⟨d, h⟩ : ∃ d, x + z + d = y + z :=
--     by simp [leq_iff_leq'] at this; assumption
--   calc
--     x + z + 1
--   _ leq x + z + d + 1 := by ring_nf; exact leq_plus
--   _ leq y + z + 1 := by rw [h]; exact Leq.Self

private lemma leq_times_of_leq : ∀ {x y z}, x leq y → x * z leq y * z
| _, _, 0, _ => Leq.Self
| x, y, z + 1, x_leq_y =>
  have : x * z leq y * z := leq_times_of_leq x_leq_y
  sorry

private lemma leq_total : ∀ {x y}, x leq y ∨ y leq x
| 0, _ => .inl zero_leq
| _, 0 => .inr zero_leq

| x + 1, y + 1 =>
  match (leq_total : x leq y ∨ y leq x) with
  | .inl x_leq_y =>
    have : x + 1 leq y + 1 := leq_plus_of_leq' x_leq_y
    .inl this

  | .inr y_leq_x =>
    have : y + 1 leq x + 1 := leq_plus_of_leq' y_leq_x
    .inr this

instance [OfNat α n] : OfNat (Option α) n where
  ofNat := some $ OfNat.ofNat n

instance [Neg α] : Neg $ Option α where
  neg := (Neg.neg <$> .)

mutual
/-
-----------
 IsEven 0

IsOdd n                   IsEven n
---------------          ---------------
IsEven (n + 1)            IsOdd (n + 1)
-/
  inductive IsEven : ℕ → Prop where
  | even_zero : IsEven 0
  | even_succ_of_odd (odd : IsOdd n) : IsEven <| n + 1

  inductive IsOdd : ℕ → Prop where
  | odd_succ_of_even (even : IsEven n) : IsOdd <| n + 1
end

lemma odd_one : IsOdd 1 := .odd_succ_of_even .even_zero

theorem even_or_odd : ∀ {n}, IsEven n ∨ IsOdd n
| 0 => .inl .even_zero
| n + 1 =>
  match (even_or_odd : IsEven n ∨ IsOdd n) with
  | .inl .even_zero => show _ from .inr odd_one

  | .inl h_n_even =>
    have : IsOdd <| n + 1 := .odd_succ_of_even h_n_even
    show _ from .inr this

  | .inr h_n_odd =>
    have : IsEven <| n + 1 := .even_succ_of_odd h_n_odd
    show _ from .inl this

abbrev IsEven' n := ∃ k, n = 2 * k
abbrev IsOdd' n := ∃ k, n = 2 * k + 1

mutual
  theorem even'_of_even {n} : IsEven n → IsEven' n
  | .even_zero => ⟨0, rfl⟩
  | .even_succ_of_odd h_odd =>
    have ⟨k, (h : _ = 2 * k + 1)⟩ := odd'_of_odd h_odd
    show _ from ⟨k + 1, by omega⟩

  theorem odd'_of_odd {n} : IsOdd n → IsOdd' n
  | .odd_succ_of_even h_even =>
    have ⟨k, (h : _ = 2 * k)⟩ := even'_of_even h_even
    show _ from ⟨k, by omega⟩
end

mutual
  theorem even_of_even' : ∀ {n}, IsEven' n → IsEven n
  | 0, _ => .even_zero
  | n + 1, ⟨k, (h : n + 1 = 2 * k)⟩ =>
    have : IsOdd' n := ⟨k - 1, by omega⟩
    have : IsOdd n := odd_of_odd' this
    show _ from .even_succ_of_odd this

  theorem odd_of_odd' : ∀ {n}, IsOdd' n → IsOdd n
  | n + 1, ⟨k, (h : n + 1 = 2 * k + 1)⟩ =>
    have : IsEven' n := ⟨k, by omega⟩
    have : IsEven n := even_of_even' this
    show _ from .odd_succ_of_even this
end

theorem even_iff_even' {n} : IsEven n ↔ IsEven' n
where
  mp := even'_of_even
  mpr := even_of_even'

theorem odd_iff_odd' {n} : IsOdd n ↔ IsOdd' n
where
  mp := odd'_of_odd
  mpr := odd_of_odd'

theorem even'_or_odd' {n} : IsEven' n ∨ IsOdd' n :=
  by rw [←even_iff_even', ←odd_iff_odd']; exact even_or_odd

theorem even'_succ_of_odd' {n} : IsOdd' n → IsEven' (n + 1) :=
  by rw [←even_iff_even', ←odd_iff_odd']; exact .even_succ_of_odd

theorem odd'_succ_of_even' {n} : IsEven' n → IsOdd' (n + 1) :=
  by rw [←even_iff_even', ←odd_iff_odd']; exact .odd_succ_of_even

theorem hh {n} : ∃ k, n * (n + 1) * (n + 2) = 3 * k :=
  match (even'_or_odd' : IsEven' n ∨ IsOdd' n) with
  | .inl ⟨k, (h : n = 2 * k)⟩ =>
    have := calc
          n * (n + 1) * (n + 2)
        = 2 * k * (2 * k + 1) * (2 * k + 2) := by rw [h]
      _ = 4 * k + 12 * k ^ 2 + 8 * k ^ 3 := by ring_nf
    have : ∃ k', 4 * k + 8 * k ^ 3 = 3 * k' := sorry
    sorry
  | .inr _ => sorry

theorem well_ordering_principle {S : Set ℕ} (h_S_non_empty : ∃ x, x ∈ S) :
  ∃ x ∈ S, ∀ y ∈ S, x ≤ y := sorry

theorem quot_rem {n d} (h_d_pos : d > 0)
: ∃ q, ∃ r < d, n = d * q + r :=
  let S := {r | ∃ q, n = d * q + r}
  have : ∃ r, r ∈ S := ⟨n, by aesop⟩

  have ⟨
    r₀,
    ⟨q₀, (h_n_eq_d_q₀_r₀ : n = d * q₀ + r₀)⟩,
    (h_r₀_minimal_in_S : ∀ y ∈ S, r₀ ≤ y)
  ⟩ := well_ordering_principle this

  suffices r₀ < d from ⟨q₀, r₀, this, h_n_eq_d_q₀_r₀⟩
  suffices ¬ r₀ ≥ d by omega

  show r₀ ≥ d → ⊥ from λ _ : r₀ ≥ d ↦
    have := calc
      n + d = (d * q₀) + r₀ + d := by rw [h_n_eq_d_q₀_r₀]
          _ = d * (q₀ + 1) + r₀ := by ring
    have : n = d * (q₀ + 1) + r₀ - d := by omega
    have : r₀ - d ∈ S := ⟨q₀ + 1, by omega⟩
    have : r₀ ≤ r₀ - d := h_r₀_minimal_in_S _ this
    have : d ≤ 0 ∧ d > 0:= ⟨by omega, h_d_pos⟩
    show ⊥ by omega

end MyNat
