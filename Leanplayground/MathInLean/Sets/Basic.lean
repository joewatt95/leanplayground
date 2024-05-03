import Duper
import Mathlib.Data.Set.Basic

namespace Sets

variable (s t u : Set α)

-- open Set

example : s ∩ t = t ∩ s :=
  by ext _; exact ⟨h1, h2⟩
  where
    h1 {x} : x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
      | ⟨x_in_s, x_in_t⟩ => ⟨x_in_t, x_in_s⟩

    h2 {x} : x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
      | ⟨x_in_t, x_in_s⟩ => ⟨x_in_s, x_in_t⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  λ x ⟨(x_in_s : x ∈ s), (x_in_u : x ∈ u)⟩ ↦
    have : x ∈ t := h x_in_s
    show x ∈ t ∧ x ∈ u from by duper [*]

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u :=
  λ x ⟨x_in_s, x_in_t_or_u⟩ ↦
    match x_in_t_or_u with
    | .inl x_in_t =>
      show _ from .inl (⟨x_in_s, x_in_t⟩ : x ∈ s ∩ t)
    | .inr x_in_u =>
      show _ from .inr (⟨x_in_s, x_in_u⟩ : x ∈ s ∩ u)

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
  λ x ⟨(x_in_s : x ∈ s), (x_notin_t_or_u : x ∉ t ∪ u)⟩ ↦
    have : x ∉ t
      | x_in_t => x_in_t |> .inl |> x_notin_t_or_u
    have : x ∉ u
      | x_in_u => x_in_u |> .inr |> x_notin_t_or_u
    show x ∈ (s \ t) \ u by simp only [Set.mem_diff]; duper [*]

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v
where
  mp (fs_subset_v : f '' s ⊆ v) x (x_in_s : x ∈ s) :=
    suffices f x ∈ v by simp only [Set.mem_preimage]; duper [*]
    have : f x ∈ f '' s := by simp only [Set.mem_image]; duper [*]
    show f x ∈ v from fs_subset_v this

  mpr (s_subset_preimg_v : s ⊆ f ⁻¹' v) y (y_in_fs : y ∈ f '' s) :=
    have : ∀ x ∈ s, f x ∈ v
      | x, x_in_s =>
        have : x ∈ f ⁻¹' v := s_subset_preimg_v x_in_s
        by simp only [Set.mem_image, Set.mem_preimage] at *; duper [*]
    have : ∃ x ∈ s, f x = y := by simp only [Set.mem_image] at *; duper [*]
    show y ∈ v by duper [*]

end Sets
