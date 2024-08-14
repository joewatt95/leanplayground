import Batteries.Classes.SatisfiesM

import Leanplayground.Prob.CVM.Algo

namespace CVM

variable
  {m : ℕ+}
  {ε δ : Set.Ioo (α := ℝ) 0 1}

lemma SatisfiesM_estimateSize_empty_list :
  SatisfiesM (. = .ok 0) <| runEstimateSize m ε δ [] := by
  simp only [runEstimateSize, estimateSize, initialState]
  apply SatisfiesM.map_pre
  apply SatisfiesM.bind_pre
  apply SatisfiesM.map_pre
  apply SatisfiesM.pure
  apply SatisfiesM.pure
  simp_all

example :
  ∃ result : PMF {result // result = .ok 0},
    Subtype.val <$> result = runEstimateSize m ε δ [] :=
  have : SatisfiesM (. = .ok 0) <| runEstimateSize m ε δ [] :=
    SatisfiesM_estimateSize_empty_list
  by simp_all [SatisfiesM]

-- lemma SatisfiesM_estimateSize_error {stream : List <| Fin m} :
--   SatisfiesM (. = .error default) <| runEstimateSize m ε δ stream := by
--   sorry

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
