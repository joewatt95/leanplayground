import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Leanplayground.MathInLean.Utils.Tactic

namespace PMF

instance : CommApplicative PMF where
  commutative_prod _ _ := by
    simp [Seq.seq, Functor.map]
    exact PMF.bind_comm _ _ _

lemma option_rec_eq_match {a : Option α} {f : α → β} {x : β} :
  Option.rec x f a = match a with
                     | some a => f a
                     | none => x := by
  cases a; all_goals simp only

attribute [simp]
  OptionT.run OptionT.mk
  Functor.map
  bind OptionT.bind
  pure OptionT.pure
  option_rec_eq_match

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

/-
This runs the `OptionT` transformer to invert the monad stack, so that we can
unwrap `PMF.bind` and reason with it.
-/
lemma optiont_pmf_bind_run_eq
  {p : OptionT PMF α} {f : α → OptionT PMF β}
  : p >>= f = p.run >>= Option.rec (return none) f := by aesop

lemma optiont_bind_support
  {p : OptionT PMF α} {f : α → OptionT PMF β}
  : (p >>= f).support = ⋃ a ∈ p.support, a.rec {none} (. |> f |>.support) :=

  have :
    ∀ a : Option α,
      (a.rec (return none) f : PMF <| Option β).support =
      a.rec {none} (. |> f |>.support)
    | some a => by simp
    | none =>
      Set.ext λ _ ↦ by
        simp only [Set.mem_singleton_iff]
        exact PMF.mem_support_pure_iff _ _

  calc
        (p >>= f).support
    _ = (p.run >>= Option.rec (return none) f).support                         := by rw [optiont_pmf_bind_run_eq]
    _ = ⋃ a ∈ p.run.support, (a.rec (return none) f : PMF <| Option β).support := PMF.support_bind _ _
    _ = ⋃ a ∈ p.support, a.rec {none} (. |> f |>.support)                      := by simp_all

-- lemma t
--   {f : OptionT PMF α} {g : α → OptionT PMF α}
--   : x ∈ (f.bind g).support ↔
--     ∃ a, a ∈ f.support ∧ x = none ∨ x ∈ g.support :=
--   sorry

lemma optiont_bind_support'
  {p : OptionT PMF α} {f : α → OptionT PMF β}
  : (p >>= f).support =
    {a | ∃ a' ∈ p.support,
      a ∈ (a'.rec {none} (. |> f |>.support) : Set <| Option β)} := by
  rw [optiont_bind_support]; ext; simp

lemma mem_optiont_pmf_bind_support
  {p : OptionT PMF α} {f : α → OptionT PMF β}
  (h : a ∈ (p >>= f).support)
  : a = none ∨ ∃ a', some a' ∈ p.support ∧ a ∈ (f a').support :=
  have ⟨as, ⟨a', h⟩, (_ : a ∈ as)⟩ :
    a ∈ ⋃ a ∈ p.support, Option.rec {none} (. |> f |>.support) a :=
    by rwa [optiont_bind_support] at h

  match a with
  | none => Or.inl rfl
  | some a =>
    have : a' ∈ p.support := by aesop
    have : some a ∈ (Option.rec {none} (. |> f |>.support) a' : Set <| Option β) := by aesop
    match a' with
    | none => by aesop
    | some a' => Or.inr ⟨a', ‹_›, by aesop⟩

example
  [MeasurableSpace α] [MeasurableSingletonClass α]
  -- [MeasurableSpace <| Option α] [MeasurableSingletonClass <| Option α]
  {p : OptionT PMF α} {f : α → OptionT PMF β}

  -- `∑' a : α, p.run a * (f a).run none` is the probability that `f a` fails
  -- (ie `none` was sampled from `f a`) given that `p` succeeds, ie
  -- (`some a` was sampled from `p`) or equivalently, the probability that
  -- `p >>= f` fails given that `f` succeeds
  (h : ∑' a : α, p.run a * (f a).run none ≤ ε)

  -- `∀ a, some a ∈ p.support → (f a).run none ≤ ε` is too weak of an assumption.
  -- The conclusion bounds the probability of failure (ie sampling `none`) of a
  -- *single* run of `f` on each input `a` that is reachable by `p` (ie in the
  -- support of `f`) by `ε`.
  -- This alone is insufficient to bound the probability of failure
  -- *across all runs* by `ε`.
  -- This could work if we change `≤ ε` to `≤ ε / p.support.card` but would
  -- likely also require additional restrictions on `p.support.card`.

  : (p >>= f).run none ≤ p.run none + ε :=
  calc
        (p >>= f).run none
    _ = (p.run >>= Option.rec (return none) f) none
      := by rw [optiont_pmf_bind_run_eq]; rfl
    _ = (∑' a : Option α,
          p.run a * (a.rec (return none) f : PMF <| Option β) none)
      := by simp only [OptionT.run, option_rec_eq_match]; rfl
    _ = p.run none + ∑' a : α, p.run a * (f a).run none
      -- How to split sum?
      := sorry
    _ ≤ p.run none + ε := by gcongr

end PMF
