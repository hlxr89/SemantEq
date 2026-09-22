import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) : ∃ δ > 0, ∀ (p : X), p ∈ K → ∀ (q : X), q ∈ F → dist p q > δ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_21a {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  rcases dummy_assumed (K := K) (F := F) hK hF hKF with ⟨δ, hδ, hdist⟩
  exact ⟨δ, hδ, fun p q hp hq => hdist p hp q hq⟩
