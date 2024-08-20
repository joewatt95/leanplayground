import Batteries.Classes.SatisfiesM

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments
import Mathlib.Probability.ProbabilityMassFunction.Integrals

import Leanplayground.Prob.CVM.Algo

namespace CVM

variable
  {m : ℕ+}
  {ε δ : Set.Ioo (α := ℝ) 0 1}

attribute [simp]
  ExceptT.run ExceptT.mk
  Functor.map ExceptT.map
  bind ExceptT.bind
  pure ExceptT.pure

example : estimateSize m ε δ [] = return 0 := by
  simp [estimateSize, estimateSize.result, initialState, initialTrace]

-- lemma SatisfiesM_estimateSize_empty_list :
--   SatisfiesM (. = .ok 0) <| runEstimateSize m ε δ [] := by
--   simp only [runEstimateSize, estimateSize, initialState]
--   apply SatisfiesM.map_pre
--   apply SatisfiesM.bind_pre
--   apply SatisfiesM.map_pre
--   apply SatisfiesM.pure
--   apply SatisfiesM.pure
--   simp_all

-- example :
--   ∃ result : PMF {result // result = .ok 0},
--     Subtype.val <$> result = runEstimateSize m ε δ [] :=
--   have : SatisfiesM (. = .ok 0) <| runEstimateSize m ε δ [] :=
--     SatisfiesM_estimateSize_empty_list
--   by simp_all [SatisfiesM]

-- example : runEstimateSize m ε δ [] = PMF.pure (Except.ok 0) := by
--   simp [estimateSize, runEstimateSize]

-- lemma SatisfiesM_estimateSize_error {stream : List <| Fin m} :
--   SatisfiesM (. = .error default) <| runEstimateSize m ε δ stream := by
--   sorry

-- example :
--   ∀ xs : List <| Fin m, xs = [] → SatisfiesM (. = 0) (estimateSize m ε δ xs) :=
--   λ xs (_ : xs = []) ↦ by
--     simp only [estimateSize, ‹xs = []›]
--     apply SatisfiesM.bind (p := (. = initialState m))
--     . sorry
--     . simp_all [initialState]
--       intros
--       sorry

end CVM
