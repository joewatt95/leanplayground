
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

noncomputable abbrev thresh : ℕ+ :=
  let thresh := ⌈(12 / ε^2) * Real.log2 ((8*m) / δ)⌉₊
  have : 0 < thresh :=
    have : (0 : ℝ) < (12 / ε^2) :=
      have : (0 : ℝ) < 12 := Nat.ofNat_pos
      have : (0 : ℝ) < ε^2 := by
        have := ε.prop.1
        simp_all only [Nat.ofNat_pos, gt_iff_lt, pow_pos]
      div_pos ‹_› ‹_›
    have : 0 < Real.log2 ((8*m) / δ) :=
      have : (1 : ℝ) < 2 := by
        simp_all only [gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_left, Nat.one_lt_ofNat]
      have : (1 : ℝ) < (8*m) / δ :=
        have := calc
          δ < (1 : ℝ) := by exact δ.prop.2
          _ ≤ m := have := m.prop; by aesop
          _ ≤ 8 * m := by aesop
        have : (0 : ℝ) < δ := δ.prop.1
        by duper [*, one_lt_div] {portfolioInstance := 1}
      Real.logb_pos ‹_› ‹_›
    by duper [*, Nat.ceil_pos, mul_pos] {portfolioInstance := 1}
  ⟨thresh, this⟩

@[ext]
structure State where
  p : Set.Ioc (α := ℝ≥0∞) 0 1
  χ : {S : Finset <| Fin m // S.card < thresh m ε δ}

noncomputable def initialState : State m ε δ where
  p := ⟨1, zero_lt_one, Preorder.le_refl _⟩
  χ := ⟨∅, have := thresh m ε δ |>.prop; by simp_all⟩

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
    step (state : State m ε δ) (x : Fin m)
      : ExceptT Unit PMF <| State m ε δ := do
      let ⟨p, (_ : 0 < p), (_ : p ≤ 1)⟩ := state.p
      let χ := state.χ

      let b : Bool ← PMF.bernoulli _ ‹p ≤ 1›

      let χ₀ := χ
        |>.val
        |>.erase x
        |> if b then id else insert x

      have : χ₀.card ≤ thresh m ε δ :=
        if _ : b
        then calc
          χ₀.card = (χ |>.val |>.erase x).card := by simp_all [χ₀]
                _ ≤ χ.val.card                 := Finset.card_erase_le
                _ ≤ thresh m ε δ               := le_of_lt χ.prop
        else calc
          χ₀.card = (χ |>.val |>.erase x |> insert x).card := by simp_all [χ₀]
                _ ≤ (χ |>.val |>.erase x).card + 1         := Finset.card_insert_le _ _
                _ ≤ χ.val.card + 1                         := by gcongr; exact Finset.erase_subset _ _
                _ ≤ thresh m ε δ                           := by omega

      if _h_card_eq_thresh : χ₀.card < thresh m ε δ
      then return { state with χ := ⟨χ₀, ‹χ₀.card < thresh m ε δ›⟩ } else

      have : χ₀.card = thresh m ε δ := by omega

      let χ₁' : Finset {x : Fin m // x ∈ χ₀} ← χ₀
        |>.attach
        |> Finset.filterM λ _ ↦
            have : ((1 : ℝ≥0∞) / 2) ≤ 1 := ENNReal.half_le_self
            PMF.bernoulli _ this

      let χ₁ : Finset <| Fin m := Function.Embedding.subtype _ <$> χ₁'

      have : ∀ x ∈ χ₁, ∃ pf : x ∈ χ₀, ⟨x, pf⟩ ∈ χ₁' := by aesop
      have : χ₁ ⊆ χ₀ := λ _ _ ↦ by duper [*] {portfolioInstance := 7}

      have : χ₁.card ≤ thresh m ε δ := by
        apply Finset.card_le_card at this
        simp_all [Finset.card_le_card]

      if _h_card_eq_thresh : χ₁.card = thresh m ε δ
      then throw () else

      let χ : { S : Finset <| Fin m // S.card < thresh m ε δ } :=
        ⟨χ₁, by omega⟩

      let p : Set.Ioc (α := ℝ≥0∞) 0 1 :=
        have := calc
          p / 2 ≤ p := by exact ENNReal.half_le_self
              _ ≤ 1 := ‹_›
        ⟨p / 2, by aesop⟩

      return { state with p := p, χ := χ }

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
