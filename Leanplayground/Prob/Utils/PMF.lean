import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace PMF

instance : CommApplicative PMF where
  commutative_prod _ _ := by
    simp [Seq.seq, Functor.map]
    exact PMF.bind_comm _ _ _

end PMF
