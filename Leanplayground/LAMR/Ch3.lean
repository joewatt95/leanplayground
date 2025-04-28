import Mathlib.Data.List.Defs
import Mathlib.Data.List.Iterate

import Leanplayground.MathInLean.Utils.Tactic

def gcd (m n : ℕ) : ℕ :=
  if h : n = 0
  then m
  else
    have : n > 0 := by omega
    have : m % n < n := Nat.mod_lt _ this
    gcd n (m % n)

namespace List

def rotations {α} (xs : List α) : List <| List α :=
  iterate go xs xs.length
  where
    go
      | [] => []
      | x :: xs => xs ++ [x]

lemma test : ∀ {xs xs' : List α} {x},
  x ∈ xs → xs' ∈ xs.rotations → x ∈ xs'
  | [], _, _ => by simp [rotations]
  | x :: xs, xs', x' => by
    simp_all [rotations, rotations.go]
    sorry

lemma nil_notin_rotations {α} :
  ∀ {xs : List α}, [] ∉ xs.rotations
  | [], _ | [_], _ => by simp [rotations] at *
  | x :: x' :: xs, (_ : [] ∈ (x :: x' :: xs).rotations) =>
    have ⟨m, (_ : m < xs.length), (_ : rotations.go^[m] (xs ++ [x, x']) = [])⟩ :
      ∃ m < _, _ := by
      simp_all [rotations, rotations.go]

    match m with
    | 0 => show ⊥ by simp_all
    | m + 1 => by
      simp_all [rotations, rotations.go]
      sorry

    -- have : [] ∈ (x' :: xs).rotations := by
    --   simp [rotations, rotations.go] at *
    --   sorry

    -- show ⊥ from nil_notin_rotations this

def perms {α} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    xs.perms.flatMap (rotations ∘ (x :: .))

lemma length_eq_length_of_mem_rotations {α} :
  ∀ {xs xs' : List α}, xs' ∈ rotations xs → xs'.length = xs.length
  | [], _ => by simp [rotations]

  | x :: xs, x' :: xs' =>
    sorry

  | _ :: _, [] => by
    sorry

lemma length_rotations_eq {α} {xs : List α} :
  (List.rotations xs).length = xs.length := by
  simp [List.rotations, List.length_iterate]

-- lemma List.length_flatMap_rotations_eq {α} {xs : List <| List α} :
--   (xs.flatMap List.rotations).length = sorry :=
--   sorry

open Nat in
lemma length_perms_eq_factorial_length {α} {xs xs' : List α}:
  xs' ∈ perms xs → xs'.length = xs.length :=
  match xs with
  | [] => by simp [perms]
  | y :: ys =>
    have :
      ∀ ys' ∈ perms ys, xs' ∈ rotations (y :: ys') →
      xs'.length = ys.length + 1 := by
      simp [rotations]
      sorry

    show _ by simpa [perms]

  -- (perms xs).length = (xs.length)! :=
  -- sorry

  -- | [] => by simp only [perms, List.length_cons, List.length_nil, zero_add, factorial_zero]
  -- | x :: xs => calc
  --     (List.perms <| x :: xs).length
  -- _ = List.sum (xs |> perms |>.map (List.length . + 1)) := by
  --     simp [perms, List.rotations]
  -- _ = ((x :: xs).length)! := by
  --     simp [factorial_succ]
  --     sorry

end List
