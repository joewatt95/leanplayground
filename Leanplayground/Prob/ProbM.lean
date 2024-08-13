import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Prob

universe u

structure Error : Type u where
  message := "Error occured!"
  deriving BEq, Ord, Hashable, Repr, Inhabited

abbrev ProbM (σ : Type u) := StateT σ <| ExceptT Error PMF

end Prob
