-- import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Iterate

import Leanplayground.MathInLean.Utils.Tactic

-- set_option trace.profiler true

def gcd (m n : ℕ) : ℕ :=
  if _ : n = 0 then m
  else
    have : m % n < n := Nat.mod_lt _ <| by omega
    gcd n <| m % n

namespace List

lemma map_const_eq_replicate {α β} {xs : List α} {c : β} :
  xs.map (λ _ ↦ c) = replicate xs.length c :=
  match xs with
  | [] | _ :: xs => by
    simp [replicate_succ, map_const_eq_replicate (xs := xs)]

lemma sublists_length_eq_2_pow_length {α} {xs : List α} :
  xs.sublists.length = 2 ^ xs.length :=
  match xs with
  | [] => by simp [sublists]
  | x :: xs => calc
      (x :: xs).sublists.length
  _ = xs.sublists.length * 2 := by simp [sublists, map_const_eq_replicate]
  _ = 2 ^ (xs.length + 1) := by
      aesop (add norm sublists_length_eq_2_pow_length)

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

abbrev perms {α} : List α → List (List α) :=
  foldr (init := [[]]) λ x ↦ flatMap <| rotations ∘ (x :: .)

lemma length_eq_length_of_mem_perms {α} {xs ys : List α}
  (_ : ys ∈ xs.perms) : ys.length = xs.length :=
  match xs with
  | [] => by aesop
  | x :: xs =>
    have ⟨zs, n, (_ : zs ∈ xs.perms), (_ : ys = rotateLeft^[n] (x :: zs))⟩ :
      ∃ _ _ _, _ := by aesop
    calc
        ys.length
    _ = zs.length + 1 := by simp_all
    _ = xs.length + 1 := congrArg _ <| length_eq_length_of_mem_perms ‹zs ∈ xs.perms›
    _ = (x :: xs).length := by simp

open Nat in
lemma length_perms_eq_factorial_length {α} {xs : List α} :
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

  _ = (xs.length + 1) * (xs.length)! := congrArg _ length_perms_eq_factorial_length

  _ = (x :: xs |>.length)! := by aesop

end List
