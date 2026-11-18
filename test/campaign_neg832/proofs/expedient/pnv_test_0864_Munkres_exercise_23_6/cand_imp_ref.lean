import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] {A : Set X} {x : X} (hA : IsClosed A) (hxA : x ∈ closure A) (hxXA : x ∉ A) (h : ∀ {U V : Set X}, IsOpen U → IsOpen V → x ∈ U ∩ V → (U ∩ A).Nonempty → (V ∩ Aᶜ).Nonempty → Set.Nonempty (U ∩ V ∩ frontier A)) : x ∈ frontier A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  by_contra hf
  have hcover : C ⊆ (closure Aᶜ)ᶜ ∪ (closure A)ᶜ := by
    intro x hx
    by_cases hxA : x ∈ closure Aᶜ
    · right
      intro hxA'
      have : x ∈ C ∩ frontier A := ⟨hx, by rw [frontier_eq_closure_inter_closure]; exact ⟨hxA', hxA⟩⟩
      simpa [hf] using this
    · exact Or.inl hxA
  have hdisj : Disjoint (closure Aᶜ)ᶜ (closure A)ᶜ := by
    rw [closure_compl, compl_compl, ← interior_compl]
    exact disjoint_compl_right.mono interior_subset interior_subset
  rcases hc.isPreconnected.subset_or_subset isClosed_closure.isOpen_compl
      isClosed_closure.isOpen_compl hdisj hcover with hC | hC
  · obtain ⟨x, hxC, hxA⟩ := Set.nonempty_iff_ne_empty.mpr hCXA
    exact hC hxC (subset_closure hxA)
  · obtain ⟨x, hxC, hxA⟩ := Set.nonempty_iff_ne_empty.mpr hCA
    exact hC hxC (subset_closure hxA)
