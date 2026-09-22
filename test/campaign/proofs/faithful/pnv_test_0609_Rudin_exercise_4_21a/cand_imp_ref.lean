import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) : ∃ δ > 0, ∀ (p : X), p ∈ K → ∀ (q : X), q ∈ F → dist p q ≥ δ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_21a {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  obtain ⟨δ, hδ, hbound⟩ := dummy_assumed hK hF hKF
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro p q hp hq
  have hpq : dist p q ≥ δ := hbound p hp q hq
  linarith
