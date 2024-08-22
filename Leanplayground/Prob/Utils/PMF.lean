import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Leanplayground.MathInLean.Utils.Tactic

namespace PMF

instance : CommApplicative PMF where
  commutative_prod _ _ := by
    simp [Seq.seq, Functor.map]
    exact PMF.bind_comm _ _ _

attribute [simp]
  OptionT.run OptionT.mk
  Functor.map
  bind OptionT.bind
  pure OptionT.pure

example
  {f : OptionT PMF α} {g : α → OptionT PMF α}
  : (f.bind g).support =
  ⋃ a ∈ f.support, a.rec {none} (. |> g |>.support) :=
  have : (f.bind g) = f.run.bind (Option.rec (return none) g) :=
    suffices
      (f.bind g).run =
      OptionT.run (f.run.bind (Option.rec (return none) g))
      by aesop
    by
      simp_all
      ext a
      match a with
      | some a => sorry
      | none => sorry

  have {a : Option α} :
    (a.rec (return none) g : PMF <| Option α).support =
    a.rec {none} (. |> g |>.support) :=
    match a with
    | some a => by simp
    | none => by
      ext
      simp only [Set.mem_singleton_iff]
      exact PMF.mem_support_pure_iff _ _

  calc
        (f.bind g).support
    _ = (f.run.bind <| Option.rec (return none) g).support
      := by simp_all
    _ = ⋃ a ∈ f.run.support, (a.rec (return none) g : PMF <| Option α).support
      := PMF.support_bind _ _
    _ = ⋃ a ∈ f.support, a.rec {none} (. |> g |>.support)
      := by simp_all

example
  {f : OptionT PMF α} {g : α → OptionT PMF α}
  (h : ∀ a : α, some a ∈ f.support → (g a).run none ≤ ε)
  : (f.bind g).run none ≤ f.run none + ε :=
  match em _ with
  | .inr (_ : none ∉ (f.bind g).support) => by aesop
  | .inl (_ : none ∈ (f.bind g).support) =>

    have ⟨a, _, _⟩ :
      ∃ a ∈ f.support, none ∈ support
        (match a with | some a => g a | none => return none) :=
      PMF.mem_support_bind_iff _ _ _ |>.mp ‹_›

    match a with
    | some a =>
      have : (g a).run none ≤ ε := by aesop
      sorry
    | none => by
      simp_all
      sorry

end PMF
