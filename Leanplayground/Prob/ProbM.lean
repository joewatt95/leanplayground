import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Prob

universe u

structure Error : Type u where
  message : String
  deriving BEq, Ord, Hashable, Repr, Inhabited

abbrev ProbM (σ : Type u) : Type u → Type u :=
  ExceptT Error <| StateT σ PMF

-- abbrev ProbM (σ α : Type u) := PMF <| EStateM.Result Error σ α

end Prob
