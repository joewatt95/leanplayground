import Mathlib.Probability.Moments

import Leanplayground.Prob.ProbM

namespace Prob

variable (m : ℕ+) (ε δ : ENNReal)

structure State where
  p : ℕ
  χ : Finset <| Fin m
  i : Fin m
  thresh : ℝ

noncomputable def initialState : State m where
  p := 1
  χ := ∅
  i := ⟨0, PNat.pos _⟩
  thresh := (12 / ε.toReal^2) * Real.log ((8*m) / δ.toReal)

noncomputable def estimate
  (m : ℕ+) (ε δ : ℝ) (stream : Array <| Fin m)
  : ProbM (State m) Unit := do
    let {p, χ, thresh, i} ← get
    if h : i = m
    then pure $ χ.card / p
    else do
      modify ({ . with χ := χ.erase i })
      sorry

end Prob
