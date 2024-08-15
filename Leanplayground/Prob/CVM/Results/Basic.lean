import Batteries.Classes.SatisfiesM

import Leanplayground.Prob.CVM.Algo

namespace CVM

variable
  {m : ℕ+}
  {ε δ : Set.Ioo (α := ℝ) 0 1}

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

-- attribute [simp]
--   ExceptT.run StateT.run
--   get getThe MonadStateOf.get StateT.get
--   liftM monadLift MonadLift.monadLift ExceptT.lift
--   ExceptT.mk
--   Functor.map StateT.map ExceptT.map
--   bind StateT.bind ExceptT.bind ExceptT.bindCont
--   pure ExceptT.pure StateT.pure

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
