import Mathlib.Data.Set.Basic

namespace Utils

@[simp]
lemma nonempty_iff_exists : Nonempty α ↔ ∃ _ : α, True
where
  mp := λ ⟨x⟩ ↦ show ∃ _, True from ⟨x, trivial⟩
  mpr := λ ⟨x, _⟩ ↦ show Nonempty α from ⟨x⟩

@[simp]
lemma nonempty_subtype_iff_exists {X : Set α} : Nonempty X ↔ ∃ a, a ∈ X
where
  mp := λ ⟨⟨a, a_in_X⟩⟩ ↦ ⟨a, a_in_X⟩
  mpr := λ ⟨a, a_in_X⟩ ↦ ⟨⟨a, a_in_X⟩⟩

end Utils
