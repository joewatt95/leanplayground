import Batteries.Classes.SatisfiesM

import Mathlib.Control.Traversable.Lemmas
import Mathlib.Data.Finset.Functor
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Moments

import Leanplayground.Prob.ProbM
import Leanplayground.Prob.Utils.Log

import Leanplayground.MathInLean.Utils.Tactic

namespace Prob

open scoped Interval ENNReal

variable
  (m : ℕ+)
  (ε δ : Set.Ioo (α := ℝ) 0 1)

structure State (m : ℕ+) where
  p : {x : ℝ≥0∞ // 0 < x ∧ x ≤ 1}
  χ : Finset <| Fin m

noncomputable def initialState : State m where
  p := ⟨1, zero_lt_one, Preorder.le_refl _⟩
  χ := ∅

noncomputable abbrev thresh := ⌈(12 / ε^2) * Real.log2 ((8*m) / δ)⌉

open Classical in
noncomputable def estimateSize
  (stream : List <| Fin m)
  : ProbM (State m) <| Fin m:= do
  match h_stream_eq : stream with
  | [] => get >>= λ {p := ⟨p, _, _⟩, χ} ↦ return ⌊χ.card / p.toReal⌋

  | elem :: stream =>
    modify λ state@{χ, ..} ↦ { state with χ := χ.erase elem }

    let {p := ⟨p, _, _⟩, ..} ← get

    if ← PMF.bernoulli _ ‹p ≤ 1› then
      modify λ state@{χ, ..} ↦ { state with χ := insert elem χ }

    let {χ, ..} ← get

    if h_card_eq_thresh : χ.card = thresh then do
      _ ← χ.toList.traverse λ elem ↦ do
        if ← PMF.bernoulli _ ‹p ≤ 1› then
          modify λ state@{χ, ..} ↦ { state with χ := χ.erase elem }

      let χ ← modifyGet λ state@{χ, ..} ↦
        have := calc
          p / 2 ≤ p := by exact ENNReal.half_le_self
              _ ≤ 1 := ‹_›
        (χ, { state with p := ⟨p / 2, by aesop, this⟩ })

      if h_card_eq_thresh : χ.card = thresh then throw default

    estimateSize stream

noncomputable def runEstimateSize
  (stream : List <| Fin m)
  : PMF <| Except Error <| Fin m :=
  stream
    |> estimateSize m ε δ
    |>.run                   -- Run ExceptT
    |>.run' (initialState _) -- Run StateT

-- attribute [simp]
--   runEstimateSize estimateSize initialState
  -- ExceptT.run StateT.run

  -- Functor.map
  -- bind ExceptT.bind StateT.bind
  -- pure ExceptT.pure StateT.pure
  -- ExceptT.mk ExceptT.run ExceptT.bindCont
  -- StateT.run

  -- get getThe MonadStateOf.get liftM monadLift MonadLift.monadLift
  -- StateT.run' StateT.get
  -- ExceptT.run ExceptT.lift ExceptT.mk

-- set_option pp.proofs true

-- example :
--   SatisfiesM (. = .ok 0) <| runEstimateSize m ε δ [] := by
--   simp [runEstimateSize, estimateSize, initialState]
--   apply SatisfiesM.map_pre
--   apply SatisfiesM.bind_pre
--   apply SatisfiesM.map_pre
--   apply SatisfiesM.pure
--   simp only [ExceptT.bindCont]
--   sorry

example :
  ∀ xs : List <| Fin m, xs = [] → SatisfiesM (. = 0) (estimateSize m ε δ xs) :=
  λ xs (_ : xs = []) ↦ by
    unfold estimateSize
    simp
    sorry

end Prob
