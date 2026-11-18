import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] [Nonempty X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (h : K ∩ F = ∅) : ∃ δ : ℝ, δ > 0 ∧ ∀ (p : X) (q : X), p ∈ K → q ∈ F → dist p q ≥ δ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_21a {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  by_cases hKe : K = ∅
  · exact ⟨1, zero_lt_one, by simp [hKe]⟩
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hKe
    letI : Nonempty X := ⟨x⟩
    obtain ⟨δ, hδ, hdist⟩ := dummy_assumed hK hF (Set.disjoint_iff_inter_eq_empty.mp hKF)
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    intro p q hp hq
    exact (half_lt_self hδ).trans_le (hdist p q hp hq)
