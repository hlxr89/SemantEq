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
  obtain ⟨δ, hδ, hsep⟩ := dummy_assumed hK hF hKF
  refine ⟨δ / 2, div_pos hδ (by norm_num), ?_⟩
  intro p q hp hq
  exact lt_of_lt_of_le (half_lt_self hδ) (hsep p hp q hq)
