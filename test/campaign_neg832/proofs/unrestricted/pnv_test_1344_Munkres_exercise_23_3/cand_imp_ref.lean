import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {A : Set X} (hA : IsConnected A) {ι : Type*} {Ai : ι → Set X} (hAi : ∀ i, IsConnected (Ai i)) (hU : ∀ i, (Ai i ∩ A).Nonempty) : IsConnected (A ∪ ⋃ i, Ai i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X α : Type*} [TopologicalSpace X]
  {A : α → Set X}
  (hAa : ∀ a, IsConnected (A a))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ a, A₀ ∩ A a ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ a, A a)) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl hα =>
      simpa using hA
  | inr hα =>
      have hU : ∀ a, IsConnected (A₀ ∪ A a) := by
        intro a
        apply IsConnected.union
        · exact Set.nonempty_iff_ne_empty.mpr (h a)
        · exact hA
        · exact hAa a
      have hcommon : (⋂ a, (A₀ ∪ A a)).Nonempty := by
        obtain ⟨x, hx⟩ := hA.nonempty
        refine ⟨x, ?_⟩
        simp [hx]
      have hp : IsPreconnected (⋃ a, (A₀ ∪ A a)) :=
        isPreconnected_iUnion hcommon fun a => (hU a).isPreconnected
      have hn : (⋃ a, (A₀ ∪ A a)).Nonempty := by
        obtain ⟨a⟩ := hα
        exact (hU a).nonempty.mono (subset_iUnion (fun a => A₀ ∪ A a) a)
      rw [iUnion_union_distrib] at hp hn
      have hc : (⋃ _ : α, A₀) = A₀ := by
        ext x
        constructor
        · simp only [mem_iUnion]
          rintro ⟨a, hx⟩
          exact hx
        · intro hx
          simp only [mem_iUnion]
          exact ⟨Classical.choice hα, hx⟩
      rw [hc] at hp hn
      exact ⟨hn, hp⟩
