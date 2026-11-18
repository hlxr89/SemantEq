import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (A : Set X) (s : Set (Set X)) (h : ∀ (t : Set X), t ∈ s → IsConnected t) (h' : ∀ (t : Set X), t ∈ s → (A ∩ t).Nonempty) : IsConnected (A ∪ ⋃₀ s) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X α : Type*} [TopologicalSpace X]
  {A : α → Set X}
  (hAa : ∀ a, IsConnected (A a))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ a, A₀ ∩ A a ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ a, A a)) := by
  apply dummy_assumed A₀ (Set.range A)
  · intro t ht
    obtain ⟨a, rfl⟩ := ht
    exact hAa a
  · intro t ht
    obtain ⟨a, rfl⟩ := ht
    exact Set.nonempty_iff_ne_empty.mpr (h a)
