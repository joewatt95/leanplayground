import Mathlib.Data.List.Defs
import Mathlib.Data.List.Iterate

import Leanplayground.MathInLean.Utils.Tactic

def gcd (m n : ℕ) : ℕ :=
  if h : n = 0 then m
  else
    have : m % n < n := Nat.mod_lt _ <| by omega
    gcd n <| m % n

namespace List

abbrev rotations {α} (xs : List α) : List <| List α :=
  iterate rotate xs xs.length
  where
    @[reducible] rotate
      | [] => []
      | x :: xs => xs ++ [x]

@[simp]
lemma rotate_length_eq_length {α n} {xs : List α} :
  (rotations.rotate^[n] xs).length = xs.length :=
  match n with
  | 0 => by simp
  | n + 1 => calc
      (rotations.rotate^[n + 1] xs).length

  _ = (rotations.rotate <| rotations.rotate^[n] xs).length := by
    rw [Function.iterate_succ_apply']

  _ = xs.length := go rotate_length_eq_length
  where
    go {xs ys : List α}
      (_ : xs.length = ys.length) :
      (rotations.rotate xs).length = ys.length :=
      match xs, ys with
      | [], [] | _ :: _, _ :: _ => by simp_all

-- lemma length_eq_length_of_mem_rotations {α} {xs ys : List α}
--   (_ : ys ∈ xs.rotations) : ys.length = xs.length := by
--   aesop (add unsafe rotate_length_eq_length)

abbrev perms {α} : List α → List (List α)
  | [] => [[]]
  | x :: xs => xs.perms.flatMap (rotations ∘ (x :: .))

lemma length_eq_length_of_mem_perms {α} {xs ys : List α}
  (_ : ys ∈ perms xs) : ys.length = xs.length :=
  match xs with
  | [] | _ :: _ => by aesop (add unsafe length_eq_length_of_mem_perms)

lemma map_const_eq_replicate {α} {xs : List α} :
  xs.map (λ _ ↦ c) = replicate (length xs) c :=
  match xs with
  | [] | _ :: _ => by
    aesop (add unsafe map_const_eq_replicate) (add norm replicate)

open Nat in
lemma length_perms_eq_factorial_length {α} {xs : List α}:
  xs.perms.length = (xs.length)! :=
  match xs with
  | [] => by simp
  | x :: xs => calc
      (List.perms <| x :: xs).length

  _ = List.sum (xs |>.perms |>.map (List.length . + 1)) := by simp

  _ = List.sum (xs |>.perms |>.map λ _ ↦ xs.length + 1) :=
      congrArg _ <| by aesop (add unsafe length_eq_length_of_mem_perms)

  _ = (xs.length + 1) * xs.perms.length := by
      aesop (add norm map_const_eq_replicate) (add norm (by ring))

  _ = (xs.length + 1) * (xs.length)! := by rw [length_perms_eq_factorial_length]

  _ = ((x :: xs).length)! := by aesop

end List
