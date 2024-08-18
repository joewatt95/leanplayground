import Mathlib.Data.Finset.Functor

import Leanplayground.Prob.Utils.Finset
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

      have : χ₀.card = thresh m ε δ := by omega

      /-
      Here, we throw away each element of `χ₀` with probability `1/2`.
      This is modelled via filterM on `χ₀` with a monadic function that samples
      from a Bernoulli distribution.
      The result of that is bound to `χ₁`, which we then show is contained in
      χ₀ and hence has a cardinality upper bounded by that of `χ₀`, and in turn
      by thresh.

      As a technicality, we first attach each element of `χ₀` with additional
      info _at the type level_ (via a Σ type) that `x ∈ χ₀`, before performing
      the monadic bind.
      Across the bind, we define `χ₁` to be the image of the Σ type projection
      on that.

      We do this because we lose all info about the shape of the term
      (ie `χ₀.filterM ...`) being bound to a variable (ie `χ₁`) across a monadic
      bind.
      To see this, observe that `let x ← t; t'` is desugared into
      `t >>= λ x ↦ t'` so that when we work with `x` in `t'`, `x` is an
      _arbitrary_ variable that is _not_ bound to `t`.
      What we would like to do is to transfer information about `t` across
      the monadic bind.
      Since we lose all info about the term-level binding of `t` to `x`, we
      appeal to the type-level and encode the info that we want there.
      In this case, we use `Finset.attach` to transform each element `x` of
      `χ₀` into a Σ type containing info that `x ∈ χ₀`.
      This helps us prove that `χ₁ ⊆ χ₀` across the monadic bind.
      -/
      let χ₁ : Finset {x : Fin m // x ∈ χ₀} ←
        χ₀
          |>.attach
          |>.filterM λ _ ↦
              have : ((1 : ℝ≥0∞) / 2) ≤ 1 := ENNReal.half_le_self
              PMF.bernoulli _ this

      let χ₁ : Finset <| Fin m := Subtype.val <$> χ₁

      have : χ₁ ⊆ χ₀ := by simp_all [χ₁, Finset.subset_iff]

      if _h_χ₁_eq_χ₀ : χ₁ = χ₀
      then
        have : χ₁.card = thresh m ε δ := by simp_all only
        throw ()
      else

      have : χ₁.card < χ₀.card := by
        duper
          [‹χ₁ ⊆ χ₀›, ‹χ₁ ≠ χ₀›, Finset.card_lt_card, ssubset_or_eq_of_subset]
          {portfolioInstance := 1}

      let χ : {S : Finset <| Fin m // S.card < thresh m ε δ} :=
        ⟨χ₁, by rwa [‹χ₀.card = thresh m ε δ›] at this⟩

      let p : Set.Ioc (α := ℝ≥0∞) 0 1 :=
        have := calc
          p / 2 ≤ p := by exact ENNReal.half_le_self
              _ ≤ 1 := ‹_›
        ⟨p / 2, show 0 < p / 2 by aesop, this⟩

      return { state with p := p, χ := χ }

noncomputable def runEstimateSize : PMF <| Except Unit <| Fin m :=
  xs |> estimateSize m ε δ |>.run

end CVM
