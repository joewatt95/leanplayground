
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
  (xs : List <| Fin m)

noncomputable abbrev thresh := Nat.ceil <| (12 / ε^2) * Real.log2 ((8*m) / δ)

@[ext]
structure State where
  p : Set.Ioc (α := ℝ≥0∞) 0 1
  χ : {S : Finset <| Fin m // S.card ≤ thresh m ε δ}

noncomputable def initialState : State m ε δ where
  p := ⟨1, zero_lt_one, Preorder.le_refl _⟩
  χ := ⟨∅, by simp_all only [Finset.card_empty, Nat.cast_zero, zero_le]⟩

-- instance : CommApplicative PMF where
--   commutative_prod _ _ := by
--     simp [Seq.seq, Functor.map]
--     exact PMF.bind_comm _ _ _

open Classical in
noncomputable def Finset.filterM {m : Type → Type v} [Monad m]
  (p : α → m Bool) (finset : Finset α)
  : m <| Finset α :=
  List.toFinset <$> finset.toList.filterM p

open Classical in
noncomputable def estimateSize : ExceptT Unit PMF <| Fin m :=
  xs |>.foldlM step (initialState m ε δ) |>.map result
  where
    step (state : State m ε δ) (elem : Fin m)
      : ExceptT Unit PMF <| State m ε δ := do
      let ⟨p, (_ : 0 < p), (_ : p ≤ 1)⟩ := state.p
      let χ := state.χ

      let χ :=
        if ← PMF.bernoulli _ ‹p ≤ 1›
        then χ
        else
          let ⟨χ, (_ : χ.card ≤ thresh _ _ _)⟩ := χ
          let χ' := χ.erase elem
          have := calc
            χ'.card ≤ χ.card       := by exact Finset.card_erase_le
                  _ ≤ thresh _ _ _ := ‹_›
          ⟨χ', by aesop⟩

      if _h_card_eq_thresh : χ.val.card < thresh m ε δ
      then return state else

      let χ'attached : Finset {x : Fin m // x ∈ χ.val} ← χ
        |>.val
        |>.attach
        |> Finset.filterM λ _ ↦
            have : ((1 : ℝ≥0∞) / 2) ≤ 1 := ENNReal.half_le_self
            PMF.bernoulli _ this

      let χ' : Finset <| Fin m := Function.Embedding.subtype _ <$> χ'attached

      have : ∀ x' ∈ χ', ∃ (pf : x' ∈ χ.val), ⟨x', pf⟩ ∈ χ'attached := by aesop
      have : χ' ≤ χ.val := λ _ _ ↦ this _ ‹_› |>.1
      have := calc
        χ'.card ≤ χ.val.card   := by exact Finset.card_le_card this
              _ = thresh _ _ _ := by have := χ.prop; omega

      let χ' : {S : Finset <| Fin m // S.card ≤ thresh m ε δ} := ⟨χ', this⟩

      let p' : Set.Ioc (α := ℝ≥0∞) 0 1 :=
        have := calc
          p / 2 ≤ p := by exact ENNReal.half_le_self
              _ ≤ 1 := ‹_›
        ⟨p / 2, by aesop⟩

      if _h_card_eq_thresh : χ.val.card = thresh m ε
      then throw ()
      else return { state with p := p', χ := χ' }

    result (state : State m ε δ) : Fin m :=
      Nat.floor <| state.χ.val.card / state.p.val.toReal

noncomputable def runEstimateSize : PMF <| Except Unit <| Fin m :=
  xs |> estimateSize m ε δ |>.run

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
