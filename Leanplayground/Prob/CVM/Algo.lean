
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

noncomputable abbrev initialState : State m where
  p := ⟨1, zero_lt_one, Preorder.le_refl _⟩
  χ := ∅

noncomputable abbrev thresh := Nat.ceil <| (12 / ε^2) * Real.log2 ((8*m) / δ)

instance : CommApplicative PMF where
  commutative_prod {α β} (x : PMF α) (y : PMF β) :=
    sorry

open Classical in
noncomputable def estimateSize
  (stream : List <| Fin m)
  : ExceptT Unit PMF <| Fin m :=
  stream
    |>.foldlM step (initialState m)
    |>.map result
  where
    step (state : State m) (elem : Fin m) : ExceptT Unit PMF <| State m := do
      let ⟨p, _, _⟩ := state.p
      let χ := state.χ.erase elem

      let χ :=
        if ← PMF.bernoulli _ ‹p ≤ 1›
        then insert elem χ
        else χ

      let state ←
        if χ.card = thresh then
          have : (1 : ℝ≥0∞) / 2 ≤ 1 := ENNReal.half_le_self

          let χ ← χ.toList.filterM λ _ ↦ PMF.bernoulli _ this

          have := calc
            p / 2 ≤ p := by exact ENNReal.half_le_self
                _ ≤ 1 := ‹_›

          have : Multiset.Nodup ⟦χ⟧ := sorry

          pure
            { state with
                p := ⟨p/2, by aesop⟩
                χ := {val := ⟦χ⟧, nodup := this}
            }
        else
          pure state

      if state.χ.card = thresh then throw default

      pure state

    result (state : State m) : Fin m :=
      Nat.floor <| state.χ.card / state.p.val.toReal

-- open Classical in
-- noncomputable def estimateSize
--   (stream : List <| Fin m)
--   : Prob.ProbM (State m) <| Fin m:= do
--   match _h_stream_eq : stream with
--   | [] =>
--     let state ← get
--     pure <| Nat.floor <| state.χ.card / state.p.val.toReal

--   | elem :: stream =>
--     modify λ state ↦ { state with χ := state.χ.erase elem }

--     let state ← get
--     let ⟨p, _, _⟩ := state.p

--     if ← PMF.bernoulli _ ‹p ≤ 1› then
--       modify λ state ↦ { state with χ := insert elem state.χ }

--     let state ← get
--     let ⟨p, _, _⟩ := state.p

--     if _h_card_eq_thresh : state.χ.card = thresh then
--       let _ ← state.χ.toList.traverse λ elem ↦ do
--         if ← PMF.bernoulli _ ‹p ≤ 1› then
--           modify λ state ↦ { state with χ := state.χ.erase elem }

--       let χ ← modifyGet λ state ↦
--         have := calc
--           p / 2 ≤ p := by exact ENNReal.half_le_self
--               _ ≤ 1 := ‹_›
--         (state.χ, { state with p := ⟨p / 2, by aesop, this⟩ })

--       if _h_card_eq_thresh : χ.card = thresh then throw default

--     estimateSize stream

-- noncomputable def runEstimateSize
--   (stream : List <| Fin m)
--   (state : State m := initialState _)
--   : PMF <| Except Prob.Error <| Fin m :=
--   stream
--     |> estimateSize m ε δ
--     |>.run        -- Run ExceptT
--     |>.run' state -- Run StateT

end CVM
