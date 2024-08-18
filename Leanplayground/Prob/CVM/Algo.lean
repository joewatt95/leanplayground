import Mathlib.Data.Finset.Functor

import Leanplayground.Prob.Utils.Log
import Leanplayground.Prob.Utils.PMF
import Leanplayground.MathInLean.Utils.Tactic

namespace CVM

open scoped Interval ENNReal

variable
  (m : ℕ+)
  (ε δ : Set.Ioo (α := ℝ) 0 1)
  (xs : List <| Fin m)

noncomputable abbrev thresh : ℕ+ :=
  let thresh := ⌈(12 / ε ^ 2) * Real.log2 (8 * m / δ)⌉₊

  have : 0 < thresh :=
    have : 0 < 12 / (ε : ℝ) ^ 2 := by
      duper [ε.prop.1, Nat.ofNat_pos, pow_pos, div_pos]
        {portfolioInstance := 1}

    have : 0 < Real.log2 (8 * m / δ) :=
      have := calc
        (δ : ℝ) < 1     := by exact δ.prop.2
              _ ≤ m     := Nat.one_le_cast.mpr m.prop
              _ ≤ 8 * m := by simp
      by duper [this, δ.prop.1, one_lt_div, Real.log2_pos]
          {portfolioInstance := 1}

    by duper [*, Nat.ceil_pos, mul_pos] {portfolioInstance := 1}

  ⟨thresh, this⟩

@[ext]
structure State : Type u where
  p : Set.Ioc (α := ℝ≥0∞) 0 1
  χ : {S : Finset <| Fin m // S.card < thresh m ε δ}

noncomputable def initialState : State m ε δ where
  p := ⟨1, zero_lt_one, Preorder.le_refl _⟩
  χ := ⟨∅, by simp_all only [Finset.card_empty, PNat.mk_coe, thresh m ε δ |>.prop]⟩

open Classical in
noncomputable def Finset.filterM {m : Type → Type u} [Monad m]
  (p : α → m Bool) (finset : Finset α)
  : m <| Finset α :=
  List.toFinset <$> finset.toList.filterM p

open Classical in
noncomputable def estimateSize : ExceptT Unit PMF <| Fin m :=
  xs |>.foldlM step (initialState m ε δ) |>.map result
  where
    result (state : State m ε δ) : Fin m :=
      ⌊state.χ.val.card / state.p.val.toReal⌋₊

    step (state : State m ε δ) (x : Fin m)
      : ExceptT Unit PMF <| State m ε δ := do
      let ⟨p, (_ : 0 < p), (_ : p ≤ 1)⟩ := state.p
      let ⟨χ, (_ : χ.card < thresh m ε δ)⟩ := state.χ

      let b ← PMF.bernoulli _ ‹p ≤ 1›

      let χ₀ := χ |>.erase x |> if b then id else insert x

      have : χ₀.card ≤ thresh m ε δ :=
        match _hb : b with
        | true => calc
          χ₀.card = (χ.erase x).card := by simp [χ₀, ‹b = true›]
                _ ≤ χ.card           := Finset.card_erase_le
                _ ≤ thresh m ε δ     := le_of_lt ‹_›
        | false => calc
          χ₀.card = (χ |>.erase x |> insert x).card := by simp [χ₀, ‹b = false›]
                _ ≤ (χ.erase x).card + 1            := Finset.card_insert_le _ _
                _ ≤ χ.card + 1                      := by gcongr; exact Finset.erase_subset _ _
                _ ≤ thresh m ε δ                    := by omega

      if _h_card_eq_thresh : χ₀.card < thresh m ε δ
      then return { state with χ := ⟨χ₀, ‹χ₀.card < thresh m ε δ›⟩ } else

      /-
        Here, we throw away each element of χ₀ with probability 1/2.
        This is modelled via filterM on χ₀ with a monadic function that samples
        from a Bernoulli distribution.
        The result of that is bound to χ₁, which we then show is contained in
        χ₀ and hence has a cardinality upper bounded by that of χ₀, and in turn
        by thresh.

        As a technicality, this is done via an intermediate variable χ₁', which
        we define so that its elements are exactly those of χ₁, but each
        element x is augmented with additional info _at the type level_
        (via a Σ type) that x ∈ χ₀.
        χ₁ is then defined to be the image of subtype projection on χ₁.

        We encode this info at the type level because we lose all info about
        the shape of the term being bound to a variable via monadic let binding.
        To see this, observe that `let x ← t; t'` is desugared into
        `t >>= λ x ↦ t'` so that when we work with `x` in `t'`, `x` is an
        _arbitrary_ variable that is _not_ bound to `t`.
        What we would like to do is to transfer information about `t` across
        the monadic bind.
        Since we lose all info about the term-level binding of `t` to `x`, we
        appeal to the type-level and encode the info that we want there.
        In this case, we use `Finset.attach` to transform each element x of χ₀
        into a Σ type containing info that x ∈ χ₀.
        This helps us prove that χ₁ ⊆ χ₀ across the monadic let binding.
      -/
      have : χ₀.card = thresh m ε δ := by omega

      let χ₁' : Finset {x : Fin m // x ∈ χ₀} ← χ₀
        |>.attach
        |> Finset.filterM λ _ ↦
            have : ((1 : ℝ≥0∞) / 2) ≤ 1 := ENNReal.half_le_self
            PMF.bernoulli _ this

      let χ₁ : Finset <| Fin m := Function.Embedding.subtype _ <$> χ₁'

      have : χ₁ ⊆ χ₀ := by simp_all [χ₁, Finset.subset_iff]
      have : χ₁.card ≤ χ₀.card := by gcongr

      if _h_card_eq_thresh : χ₁.card = thresh m ε δ
      then throw () else

      let χ : {S : Finset <| Fin m // S.card < thresh m ε δ} :=
        ⟨χ₁, by omega⟩

      let p : Set.Ioc (α := ℝ≥0∞) 0 1 :=
        have := calc
          p / 2 ≤ p := by exact ENNReal.half_le_self
              _ ≤ 1 := ‹_›
        ⟨p / 2, by aesop⟩

      return { state with p := p, χ := χ }

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
