import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Leanplayground.MathInLean.Utils.Tactic

namespace PMF

instance : CommApplicative PMF where
  commutative_prod _ _ := by
    simp [Seq.seq, Functor.map]
    exact PMF.bind_comm _ _ _

lemma option_rec_eq {a : Option α} {f : α → β} {x : β} :
  Option.rec x f a = match a with
                     | some a => f a
                     | none => x :=
  match a with
  | some _ | none => by simp

attribute [simp]
  OptionT.run OptionT.mk
  Functor.map
  bind OptionT.bind
  pure OptionT.pure
  option_rec_eq

lemma bind_skip {p : PMF α} {f g : α → PMF β} :
  (∀ a, f a = g a) → p.bind f = p.bind g := by aesop

example {f g : PMF ℝ} :
  (do
    let x ← f
    let y ← g
    return x + y)
  =
  do
    let x ← f
    let y ← g
    return y + x := by simp [bind_skip, add_comm]

example {f g : PMF ℝ} :
  (do
    let x ← f
    let y ← g
    return x + y)
  = do
      let y ← g
      let x ← f
      return y + x :=
  have :
    (do
      let y ← g
      let x ← f
      return x + y)
    = do
        let x ← f
        let y ← g
        return x + y :=
    PMF.bind_comm _ _ _
  by simp_all only [bind_skip, add_comm]

-- lemma optiont_bind
--   {f : OptionT PMF α} {g : α → OptionT PMF α}
--   : (f.bind g) = f.run.bind (Option.rec (return none) g) := by aesop

lemma optiont_bind_support
  {f : OptionT PMF α} {g : α → OptionT PMF α}
  : (f.bind g).support = ⋃ a ∈ f.support, a.rec {none} (. |> g |>.support) :=

  have : (f.bind g) = f.run.bind (Option.rec (return none) g) := by aesop

  have {a : Option α} :
    (a.rec (return none) g : PMF <| Option α).support =
    a.rec {none} (. |> g |>.support) :=
    match a with
    | some a => by simp
    | none =>
      Set.ext λ _ ↦ by
        simp only [Set.mem_singleton_iff]
        exact PMF.mem_support_pure_iff _ _

  calc
        (f.bind g).support
    _ = (f.run.bind <| Option.rec (return none) g).support                     := by simp_all
    _ = ⋃ a ∈ f.run.support, (a.rec (return none) g : PMF <| Option α).support := PMF.support_bind _ _
    _ = ⋃ a ∈ f.support, a.rec {none} (. |> g |>.support)                      := by simp_all

-- lemma t
--   {f : OptionT PMF α} {g : α → OptionT PMF α}
--   : x ∈ (f.bind g).support ↔
--     ∃ a, a ∈ f.support ∧ x = none ∨ x ∈ g.support :=
--   sorry

lemma optiont_bind_support'
  {f : OptionT PMF α} {g : α → OptionT PMF α}
  : (f.bind g).support =
    {a | ∃ a' ∈ f.support, a ∈ (a'.rec {none} (. |> g |>.support) : Set <| Option α)} :=

  Set.ext λ a ↦
    let φ := ∃ a', a' ∈ f.support ∧ a ∈ (a'.rec {none} (. |> g |>.support) : Set <| Option α)
    let ψ := ∃ a', a' ∈ f.support ∧ a'.rec (a = none) λ a' ↦ a ∈ (a' |> g |>.support)

    suffices φ ↔ ψ by
      rw [optiont_bind_support]
      simp [-option_rec_eq]

    have : φ → ψ :=
      λ | ⟨some a', _, _⟩ | ⟨none, _, _⟩ => by tauto

    have : ψ → φ :=
      λ | ⟨some a', _, _⟩ | ⟨none, _ , _⟩ => by tauto

    ⟨‹_›, ‹_›⟩

lemma aux'
  {f : OptionT PMF α} {g : α → OptionT PMF α}
  (h : a ∈ (f.bind g).support)
  : a = none ∨ ∃ a', some a' ∈ f.support ∧ a ∈ (g a').support :=
  have ⟨as, ⟨a', h⟩, (_ : a ∈ as)⟩ :
    a ∈ ⋃ a ∈ f.support, Option.rec {none} (. |> g |>.support) a :=
    by rwa [optiont_bind_support] at h

  match a with
  | none => Or.inl rfl
  | some a =>
    have : a' ∈ f.support := by aesop
    have : some a ∈ (Option.rec {none} (. |> g |>.support) a' : Set <| Option α) := by aesop
    match a' with
    | none => by aesop
    | some a' => Or.inr ⟨a', ‹_›, by aesop⟩

open Classical in
example
  [MeasurableSpace α] [MeasurableSingletonClass α]
  -- [MeasurableSpace <| Option α] [MeasurableSingletonClass <| Option α]
  {f : OptionT PMF α} {g : α → OptionT PMF α}

  -- `∑' a : α, f.run a * (g a).run none` is the probability that `g a` fails
  -- (ie `none` was sampled from `g a`) given that `f` succeeds, ie
  -- (`some a` was sampled from `f`) or equivalently, the probability that
  -- `f.bind g` fails given that `f` succeeds
  (h : ∑' a : α, f.run a * (g a).run none ≤ ε)

  -- `∀ a, some a ∈ f.support → (g a).run none ≤ ε` is too weak of an assumption.
  -- The conclusion bounds the probability of failure (ie sampling `none`) of a
  -- *single* run of `g` on each input `a` that is reachable by `f` (ie in the
  -- support of `f`) by `ε`.
  -- This alone is insufficient to bound the probability of failure
  -- *across all runs_* by `ε`.
  -- This could work if we change `≤ ε` to `≤ ε / f.support.card` but `h` is
  -- likely the weakest assumption we can have.

  : (f.bind g).run none ≤ f.run none + ε :=
  calc
        (f |>.bind g |>.run) none
      -- This `bind` is `OptionT.bind`, *NOT* the probabilistic `PMF.bind`
    _ = f.run.bind (Option.rec (return none) g) none
      -- Run the `OptionT` transformer to invert the monad stack, so that we
      -- can unwrap `PMF.bind`.
      := by aesop
    _ = (∑' a : Option α,
          f.run a *
            (match a with
              | some a => (g a).run
              | none => return none)
              none) := by simp_all; rfl
    _ = f.run none + ∑' a : α, f.run a * (g a).run none
      -- How to split sum?
      := sorry
    _ ≤ f.run none + ε := by gcongr

end PMF
