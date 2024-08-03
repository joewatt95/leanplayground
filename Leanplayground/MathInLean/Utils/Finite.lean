import Mathlib.Data.Finset.Lattice

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
    ⨅ x ∈ s, I x = ⨅ x ∈ insert a s', I x := by aesop
               _ = I a ⊓ ⨅ x ∈ s', I x    := Finset.iInf_insert _ _ _

end Finite
