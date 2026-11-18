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
  obtain ⟨ε, hε, hdist⟩ := dummy_assumed hAB hA hB
  refine ⟨⋃ x ∈ A, Metric.ball x (ε / 2), ⋃ y ∈ B, Metric.ball y (ε / 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  · exact isOpen_iUnion fun y ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  · intro x hx
    exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx (Metric.mem_ball_self (half_pos hε)))
  · intro y hy
    exact Set.mem_iUnion_of_mem y (Set.mem_iUnion_of_mem hy (Metric.mem_ball_self (half_pos hε)))
  · rw [Set.disjoint_iUnion_left]
    intro x
    rw [Set.disjoint_iUnion_left]
    intro hx
    rw [Set.disjoint_iUnion_right]
    intro y
    rw [Set.disjoint_iUnion_right]
    intro hy
    apply Metric.ball_disjoint_ball
    simpa only [add_halves] using hdist x hx y hy
