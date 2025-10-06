import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Leanplayground.MathInLean.Utils.Tactic

variable {α β : Type}

@[ext]
class IsCoupling
  {m : (Type → Type) → Type → Type} [Monad <| m PMF]
  (c : m PMF <| α × β) (p : m PMF α) (q : m PMF β) where
  map_fst : Prod.fst <$> c = p
  map_snd : Prod.snd <$> c = q

abbrev SPMF := OptionT PMF

#check IsCoupling (m := (. <| .)) (sorry : PMF (α × β)) (sorry : PMF α) (sorry : PMF β)
#check IsCoupling (sorry : SPMF (α × β)) (sorry : SPMF α) (sorry : SPMF β)

example {a : α} : (return a : SPMF α) = (return a : PMF α) := by simp
