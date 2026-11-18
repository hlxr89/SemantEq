import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {A B : Set X} (hAB : Disjoint A B) (hA : IsClosed A) (hB : IsClosed B): ∃ (ε : ℝ), ε > 0 ∧ ∀ x ∈ A, ∀ y ∈ B, dist x y ≥ ε := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B := by
  rcases dummy_assumed hAB hA hB with ⟨ε, hε, hdist⟩
  refine ⟨⋃ x ∈ A, Metric.ball x (ε / 2), ⋃ y ∈ B, Metric.ball y (ε / 2),
    isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball,
    isOpen_iUnion fun y ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, Metric.mem_ball_self (half_pos hε)⟩
  · intro y hy
    simp only [Set.mem_iUnion]
    exact ⟨y, hy, Metric.mem_ball_self (half_pos hε)⟩
  · rw [Set.disjoint_left]
    intro z hzA hzB
    simp only [Set.mem_iUnion, Metric.mem_ball] at hzA hzB
    rcases hzA with ⟨x, hx, hzx⟩
    rcases hzB with ⟨y, hy, hzy⟩
    have hxy : dist x y < ε := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ < ε := by rw [dist_comm x z]; linarith
    exact (not_lt_of_ge (hdist x hx y hy)) hxy
