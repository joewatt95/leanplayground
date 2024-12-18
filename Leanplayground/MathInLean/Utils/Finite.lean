import Mathlib.Order.CompleteLattice.Finset

import Leanplayground.MathInLean.Utils.Tactic

namespace Finite

universe u v

variable
  {α : Type u} {β : Type v}

lemma Finset.iInf_erase
  [CompleteLattice β] [DecidableEq α] {s : Finset α} {I : α → β}
  {a : s}
  : ⨅ x ∈ s, I x = I a ⊓ ⨅ x ∈ s.erase a, I x :=
  let ⟨a, (_ : a ∈ s)⟩ := a
  let s' := s.erase a
  calc
        ⨅ x ∈ s, I x
    _ = ⨅ x ∈ insert a s', I x := by rw [Finset.insert_erase ‹a ∈ s›]
    _ = I a ⊓ ⨅ x ∈ s', I x    := Finset.iInf_insert _ _ _

end Finite
