import Mathlib.Data.List.Iterate

import Leanplayground.MathInLean.Utils.Tactic

-- set_option trace.profiler true

def gcd (m n : ℕ) : ℕ :=
  if h : n = 0 then m
  else
    have : m % n < n := Nat.mod_lt _ <| by omega
    gcd n <| m % n

namespace List

abbrev rotations {α} (xs : List α) : List <| List α :=
  iterate rotateLeft xs xs.length

@[simp]
lemma rotateLeft_length_eq_length {α} {xs : List α} :
  xs.rotateLeft.length = xs.length := by
  aesop (add norm rotateLeft) (add norm (by omega))

@[simp]
lemma iterate_rotateLeft_length_eq_length {α n} {xs : List α} :
  (rotateLeft^[n] xs).length = xs.length :=
  match n with
  | 0 | _ + 1 => by simp [iterate_rotateLeft_length_eq_length]

abbrev perms {α} (xs : List α) : List <| List α :=
  match xs with
  | [] => [[]]
  | x :: xs => xs.perms.flatMap (rotations ∘ (x :: .))

lemma length_eq_length_of_mem_perms {α} {xs ys : List α}
  (_ : ys ∈ perms xs) : ys.length = xs.length :=
  match xs with
  | [] | _ :: _ => by aesop (add safe length_eq_length_of_mem_perms)

lemma map_const_eq_replicate {α β} {xs : List α} {c : β} :
  xs.map (λ _ ↦ c) = replicate xs.length c :=
  match xs with
  | [] | _ :: _ => by
    aesop (add safe map_const_eq_replicate) (add norm replicate_succ)

open Nat in
lemma length_perms_eq_factorial_length {α} {xs : List α}:
  xs.perms.length = (xs.length)! :=
  match xs with
  | [] => by simp
  | x :: xs => calc
      (x :: xs).perms.length

  _ = (xs.perms.map λ ys ↦ ys.length + 1).sum := by simp

  _ = (xs.perms.map λ _ ↦ xs.length + 1).sum :=
      congrArg _ <| by aesop (add safe length_eq_length_of_mem_perms)

  _ = (xs.length + 1) * xs.perms.length := by
      aesop (add norm map_const_eq_replicate) (add norm (by ring))

  _ = (xs.length + 1) * (xs.length)! := by rw [length_perms_eq_factorial_length]

  _ = ((x :: xs).length)! := by aesop

end List
