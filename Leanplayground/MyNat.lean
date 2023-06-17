import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Basic

namespace MyNat

inductive Leq : (m n : ℕ) → Prop
| LeqSelf : Leq m m
| LeqSucc (m_leq_n : Leq m n) : Leq m (n + 1)

infix:50 "leq" => Leq

lemma zero_leq : ∀ {m}, 0 leq m
| 0 => Leq.LeqSelf
| m + 1 =>
  haveI : 0 leq m := zero_leq
  show 0 leq m.succ from Leq.LeqSucc this

macro m:term "leq'" n:term : term => `(∃ d : ℕ, $m + d = $n)

private lemma leq'_of_leq : ∀ {n}, m leq n → m leq' n
| _, (Leq.LeqSelf : m leq m) =>
  show ∃ d, m + d = m from ⟨0, rfl⟩
| .(_ + 1), (Leq.LeqSucc m_leq_n) =>
  haveI : m leq' _ := leq'_of_leq m_leq_n
  let ⟨d, h⟩ := this
  haveI : m + (d + 1) = _ + 1 := by rw [←add_assoc, h]
  show ∃ d, m + d = _ + 1 from ⟨d + 1, this⟩

private lemma eq_zero_or_succ : ∀ {n}, n = 0 ∨ ∃ m, n = m + 1
| 0 => show _ from Or.inl rfl
| n + 1 =>
  suffices ∃ m, n + 1 = m + 1 from Or.inr this

  haveI : n = 0 ∨ ∃ m, n = m + 1 := eq_zero_or_succ
  match this with
  | Or.inl (h : n = 0) =>
    haveI : n + 1 = 0 + 1 := by rw [h]
    show ∃ m, n + 1 = m + 1 from ⟨0, this⟩

  | Or.inr (⟨m, h⟩ : ∃ _m, n = _m + 1) =>
    haveI : n + 1 = (m + 1) + 1 := by rw [h]
    show ∃ m', n + 1 = m' + 1 from ⟨m + 1, this⟩

private lemma leq_of_leq' : ∀ {n}, (∃ d, m + d = n) → m leq n
| n, ⟨0, h⟩ =>
  haveI : m = n := by simp at h; exact h
  show m leq n by rw [this]; exact Leq.LeqSelf

| n + 1, ⟨d + 1, h⟩ =>
  haveI : (m + d) + 1 = n + 1 := by rw [add_assoc, h]
  haveI : ∃ d, m + d = n := ⟨d, by simp at this; exact this⟩
  haveI : m leq n := leq_of_leq' this
  show m leq n + 1 from Leq.LeqSucc this

@[simp]
theorem leq_iff_leq' : (m leq n) ↔ m leq' n :=
  ⟨leq'_of_leq, leq_of_leq'⟩ 

end MyNat