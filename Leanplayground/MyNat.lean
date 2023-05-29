import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Basic

namespace MyNat

inductive Leq : (m n : Nat) → Prop
| LeqSelf : Leq m m
| LeqSucc (m_leq_n : Leq m n) : Leq m (n + 1)

infix:50 "leq" => Leq

lemma zero_leq : ∀{m}, 0 leq m
| 0 => Leq.LeqSelf
| m + 1 =>
  haveI : 0 leq m := zero_leq
  show 0 leq m.succ from Leq.LeqSucc this

macro m:term "leq'" n:term : term => `(∃ d : ℕ, $m + d = $n)

private lemma leq'_of_leq {m} : ∀ {n}, m leq n → m leq' n
| _, (Leq.LeqSelf : m leq m) =>
  show ∃ d, m + d = m from ⟨0, rfl⟩
| .(_ + 1), (Leq.LeqSucc m_leq_n) =>
  haveI : m leq' _ := leq'_of_leq m_leq_n
  let ⟨d, h⟩ := this
  haveI : _ := calc
    m + (d + 1) = (m + d) + 1 := by rw [←add_assoc]
              _ = _ + 1       := by rw [h]
  show ∃ d, m + d = _ + 1 from ⟨d + 1, this⟩

end MyNat