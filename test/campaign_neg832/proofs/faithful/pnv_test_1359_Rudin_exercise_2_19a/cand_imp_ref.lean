import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) : ∃ (ε : ℝ), ε > 0 ∧ ∀ (x : X), x ∈ A → ∀ (y : X), y ∈ B → dist x y ≥ ε := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B := by
  obtain ⟨ε, hε, hdist⟩ := dummy_assumed hA hB hAB
  refine ⟨⋃ x ∈ A, Metric.ball x (ε / 2), ⋃ y ∈ B, Metric.ball y (ε / 2),
    isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball,
    isOpen_iUnion fun y ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨x, ⟨hx, by simpa using half_pos hε⟩⟩
  · intro y hy
    simp only [Set.mem_iUnion]
    exact ⟨y, ⟨hy, by simpa using half_pos hε⟩⟩
  · rw [Set.disjoint_left]
    rintro z hzA hzB
    simp only [Set.mem_iUnion, Metric.mem_ball] at hzA hzB
    obtain ⟨x, hxA, hzx⟩ := hzA
    obtain ⟨y, hyB, hzy⟩ := hzB
    have hxy : dist x y < ε := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ = dist z x + dist z y := by rw [dist_comm x z]
        _ < ε / 2 + ε / 2 := add_lt_add hzx hzy
        _ = ε := by ring
    exact (not_lt_of_ge (hdist x hxA y hyB)) hxy
