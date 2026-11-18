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
  cases isEmpty_or_nonempty X with
  | inl hX =>
      exact ⟨1, by norm_num, fun p => isEmptyElim p⟩
  | inr hX =>
      letI : Nonempty X := hX
      have h : K ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.mp hKF
      obtain ⟨δ, hδ, hdist⟩ := dummy_assumed hK hF h
      refine ⟨δ / 2, by linarith, ?_⟩
      intro p q hp hq
      have hpq := hdist p q hp hq
      linarith
