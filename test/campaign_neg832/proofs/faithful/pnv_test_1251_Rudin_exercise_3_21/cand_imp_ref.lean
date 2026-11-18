import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] [CompleteSpace X] {s : Set X} (hs : IsClosed s) (H : ∀ x ∈ s, 𝓝[s] x ≠ ⊥) : ∃ x ∈ s, s ⊆ closure ({x} : Set X) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_21
  {X : Type*} [MetricSpace X] [CompleteSpace X]
  (E : ℕ → Set X)
  (hEcl : ∀ n, IsClosed (E n))
  (hEne : ∀ n, (E n).Nonempty)
  (hEbdd : ∀ n, Bornology.IsBounded (E n))
  (hE : ∀ n, E n ⊇ E (n + 1))
  (hE' : Tendsto (λ n => Metric.diam (E n)) atTop (𝓝 0)) :
  ∃ a, Set.iInter E = {a} := by
  have hs : IsClosed (Set.iInter E) := isClosed_iInter hEcl
  have hH : ∀ x ∈ Set.iInter E, 𝓝[Set.iInter E] x ≠ ⊥ := by
    intro x hx
    rw [← Filter.neBot_iff, nhdsWithin_neBot]
    intro t ht
    exact ⟨x, mem_of_mem_nhds ht, hx⟩
  obtain ⟨a, ha, hsub⟩ := dummy_assumed hs hH
  have hsub' : Set.iInter E ⊆ {a} := by
    simpa only [closure_singleton] using hsub
  exact ⟨a, Set.Subset.antisymm hsub' (Set.singleton_subset_iff.mpr ha)⟩
