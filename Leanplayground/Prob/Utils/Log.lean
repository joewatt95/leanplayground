import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

import Leanplayground.MathInLean.Utils.Tactic

namespace Real

noncomputable abbrev log2 : ℝ → ℝ := logb 2

theorem log2_pos {x : ℝ} : 1 < x → 0 < log2 x :=
  Real.logb_pos Nat.one_lt_ofNat

end Real
