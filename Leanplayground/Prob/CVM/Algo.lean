
import Mathlib.Control.Traversable.Lemmas
import Mathlib.Data.Finset.Functor
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Moments

import Leanplayground.Prob.ProbM
import Leanplayground.Prob.Utils.Log

import Leanplayground.MathInLean.Utils.Tactic

namespace CVM

open scoped Interval ENNReal

variable
  (m : ℕ+)
  (ε δ : Set.Ioo (α := ℝ) 0 1)

@[ext]
structure State where
  p : {x : ℝ≥0∞ // 0 < x ∧ x ≤ 1}
  χ : Finset <| Fin m

noncomputable def initialState : State m where
  p := ⟨1, zero_lt_one, Preorder.le_refl _⟩
  χ := ∅

noncomputable abbrev thresh := ⌈(12 / ε^2) * Real.log2 ((8*m) / δ)⌉

open Classical in
noncomputable def estimateSize
  (stream : List <| Fin m)
  : Prob.ProbM (State m) <| Fin m:= do
  match h_stream_eq : stream with
  | [] => get >>= λ state ↦ return ⌊state.χ.card / state.p.val.toReal⌋

  | elem :: stream =>
    modify λ state ↦ { state with χ := state.χ.erase elem }

    let state ← get
    let ⟨p, _, _⟩ := state.p

    if ← PMF.bernoulli _ ‹p ≤ 1› then
      modify λ state ↦ { state with χ := insert elem state.χ }

    let state ← get
    let ⟨p, _, _⟩ := state.p

    if h_card_eq_thresh : state.χ.card = thresh then
      _ ← state.χ.toList.traverse λ elem ↦ do
        if ← PMF.bernoulli _ ‹p ≤ 1› then
          modify λ state ↦ { state with χ := state.χ.erase elem }

      let χ ← modifyGet λ state ↦
        have := calc
          p / 2 ≤ p := by exact ENNReal.half_le_self
              _ ≤ 1 := ‹_›
        (state.χ, { state with p := ⟨p / 2, by aesop, this⟩ })

      if h_card_eq_thresh : χ.card = thresh then throw default

    estimateSize stream

noncomputable def runEstimateSize
  (stream : List <| Fin m)
  (state : State m := initialState _)
  : PMF <| Except Prob.Error <| Fin m :=
  stream
    |> estimateSize m ε δ
    |>.run        -- Run ExceptT
    |>.run' state -- Run StateT

end CVM
