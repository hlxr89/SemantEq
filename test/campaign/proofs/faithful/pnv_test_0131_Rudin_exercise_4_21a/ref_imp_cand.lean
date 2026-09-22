import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_21a_assumed {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) : ∃ ε : ℝ, ε > 0 ∧ ∀ (p : X) (hp : p ∈ K) (q : X) (hq : q ∈ F), dist p q ≥ ε := by
  obtain ⟨δ, hδ, hsep⟩ := exercise_4_21a_assumed K F hK hF hKF
  exact ⟨δ, hδ, fun p hp q hq => (hsep p q hp hq).le⟩
