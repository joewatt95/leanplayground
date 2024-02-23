import LeanCopilot

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
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
  haveI : 0 leq m := zero_leq
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
  haveI : m leq' _ := leq'_of_leq m_leq_n
  let ⟨d, h⟩ := this
  haveI : m + (d + 1) = _ + 1 := by rw [←h]; ring
  show ∃ d, m + d = _ + 1 from ⟨d + 1, this⟩

private lemma leq_of_leq' : ∀ {n}, (∃ d, m + d = n) → m leq n
| n, ⟨0, h⟩ =>
  haveI : m = n := by simp at h; exact h
  show m leq n by rw [this]; exact Leq.Self

| n + 1, ⟨d + 1, h⟩ =>
  haveI : (m + d) + 1 = n + 1 := by rw [add_assoc, h]
  haveI : ∃ d, m + d = n := ⟨d, by simp at this; assumption⟩
  haveI : m leq n := leq_of_leq' this
  show m leq n + 1 from this.Succ

@[simp]
theorem leq_iff_leq' : (m leq n) ↔ m leq' n :=
  ⟨leq'_of_leq, leq_of_leq'⟩

private lemma Leq.reflexive : x leq x := Leq.Self

private lemma Leq.transitive : (x leq y) → (y leq z) → x leq z
| x_leq_y, y_leq_z =>
  have ⟨d1, h1⟩ : ∃ d1, x + d1 = y :=
    by simp [leq_iff_leq'] at x_leq_y; assumption
  have ⟨d2, h2⟩ : ∃ d2, y + d2 = z :=
    by simp [leq_iff_leq'] at y_leq_z; assumption
  haveI : ∃ d, x + d = z := ⟨d1 + d2, by ring_nf; rw [h1, h2]⟩
  show x leq z by rw [←leq_iff_leq'] at this; assumption

instance : Trans Leq Leq Leq := ⟨Leq.transitive⟩

private lemma Leq.antisymmetric : x leq y → y leq x → x = y
| x_leq_y, y_leq_x =>
  have ⟨d1, h1⟩ : ∃ d1, x + d1 = y :=
    by simp [leq_iff_leq'] at x_leq_y; assumption
  have ⟨d2, h2⟩ : ∃ d2, y + d2 = x :=
    by simp [leq_iff_leq'] at y_leq_x; assumption
  haveI : x + (d1 + d2) = x := by rw [←h1] at h2; ring_nf; assumption
  haveI : d1 + d2 = 0 := Nat.add_left_cancel this
  haveI : d1 = 0 :=
    match (eq_zero_or_succ : d1 = 0 ∨ ∃ d, d1 = d + 1) with
    | .inl d1_eq_zero => d1_eq_zero
    | .inr ⟨d, d1_eq_d_succ⟩ =>
      suffices ⊥ from this.elim
      haveI : d + d2 + 1 = 0 := by ring_nf; simp [d1_eq_d_succ] at this
      show ⊥ from Nat.succ_ne_zero _ this
  show x = y by rw [this] at h1; exact h1

private lemma leq_plus : ∀ {b}, a leq a + b
| 0 => .Self
| b + 1 => calc
  a leq a + b     := leq_plus
  _ leq a + b + 1 := by simp

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
      _ = _ + 1 + _ + 1 := by simp; ring_nf

private lemma h :
  ∀ {as bs : List α},
    (∀ (i : Fin as.length), ∃ j : Fin bs.length, i.val = j) →
    as.length ≤ bs.length

| [], _, _ | a :: as, [], _ => by aesop

| a :: as, b :: bs, h =>
  suffices as.length ≤ bs.length from sorry
  suffices ∀ (i : Fin as.length), ∃ j : Fin bs.length, i.val = j from sorry
  λ ⟨i, h_i⟩ ↦
    haveI : as.length < (a :: as).length := by aesop
    let i' : Fin (a :: as).length := ⟨i, by omega⟩
    haveI := h i'
    sorry
    -- ⟨⟨i.pred, sorry⟩, sorry⟩

private lemma leq_sum_of_leq :
∀ {as bs : List ℕ},
  (∀ i, ∃ j, i.val = j.val ∧ as.get i ≤ bs.get j) →
  as.length ≤ bs.length ∧ as.sum ≤ bs.sum

| [], _, _ | a :: as, [], h => by aesop

| a :: as, b :: bs, h =>
  -- haveI : as.length ≤ bs.length := by aesop
  haveI : as.length < (a :: as).length := by aesop
  have : ∀ i, ∃ j, i.val = j.val ∧ as.get i ≤ bs.get j
    | ⟨i, _⟩ =>
      let ⟨⟨i, h_i⟩, _, h⟩ := h ⟨i, by omega⟩
      match i with
      | 0 => sorry
      | i + 1 =>
        ⟨⟨i.pred, sorry⟩, sorry, sorry⟩
  sorry

  -- haveI : as.length = bs.length := by aesop
  -- haveI := calc
  --   as.length + 1 = (a :: as).length := by aesop
  --               _ = (b :: bs).length := by aesop
  --               _ = bs.length + 1 := by aesop
  -- sorry

--   haveI h_len : as.length = bs.length := by aesop
--   haveI :
--     ∀ i (_ : i.val < as.length),
--       as.get i ≤ bs.get ⟨i.val, by linarith⟩ :=
--     λ i h' ↦
--       haveI := calc
--         i.val < as.length := by exact h'
--         _ < (a :: as).length := by aesop
--       haveI := h ⟨i.val, by aesop⟩ this
--       sorry
--   sorry

-- | a :: as, b :: bs, h =>
--   suffices as.sum leq bs.sum from sorry
--   haveI : ∀ i, ∃ j, j.val = i.val ∧ as.get i leq bs.get j := by aesop
--   sorry

private lemma leq_plus_of_leq' : a leq b → a + c leq b + c :=
  (leq_plus_of_leq . .Self)

-- private lemma leq_plus_of_leq : ∀ {x y z}, x leq y → x + z leq y + z
-- | _, _, 0, x_leq_y => x_leq_y
-- | x, y, z + 1, x_leq_y =>
--   haveI : x + z leq y + z := leq_plus_of_leq x_leq_y
--   have ⟨d, h⟩ : ∃ d, x + z + d = y + z :=
--     by simp [leq_iff_leq'] at this; assumption
--   calc
--     x + z + 1
--   _ leq x + z + d + 1 := by ring_nf; exact leq_plus
--   _ leq y + z + 1 := by rw [h]; exact Leq.Self

private lemma leq_times_of_leq : ∀ {x y z}, x leq y → x * z leq y * z
| _, _, 0, _ => Leq.Self
| x, y, z + 1, x_leq_y =>
  haveI : x * z leq y * z := leq_times_of_leq x_leq_y
  sorry

private lemma leq_total : ∀ {x y}, x leq y ∨ y leq x
| 0, _ => .inl zero_leq
| _, 0 => .inr zero_leq

| x + 1, y + 1 =>
  match (leq_total : x leq y ∨ y leq x) with
  | .inl x_leq_y =>
    haveI : x + 1 leq y + 1 := leq_plus_of_leq' x_leq_y
    .inl this

  | .inr y_leq_x =>
    haveI : y + 1 leq x + 1 := leq_plus_of_leq' y_leq_x
    .inr this

instance [OfNat α n] : OfNat (Option α) n where
  ofNat := some $ OfNat.ofNat n

instance [Neg α] : Neg $ Option α where
  neg := (Neg.neg <$> .)

end MyNat
