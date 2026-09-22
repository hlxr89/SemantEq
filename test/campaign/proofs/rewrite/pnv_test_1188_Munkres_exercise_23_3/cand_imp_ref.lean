import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (A : Set X) (B : ι → Set X) (hA : IsConnected A) (hB : ∀ i, IsConnected (B i)) (h : ∀ i, (B i) ∩ A ≠ ∅) : IsConnected (A ∪ (⋃ i, B i)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X α : Type*} [TopologicalSpace X]
  {A : α → Set X}
  (hAa : ∀ a, IsConnected (A a))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ a, A₀ ∩ A a ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ a, A a)) := by
  apply dummy_assumed A₀ A hA hAa
  intro a
  simpa only [inter_comm] using h a
