import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hDisjoint : Disjoint K F) : ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ F, dist p q > δ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_21a {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  obtain ⟨δ, hδ, hdist⟩ := dummy_assumed hK hF hKF
  exact ⟨δ, hδ, fun p q hp hq => hdist p hp q hq⟩
