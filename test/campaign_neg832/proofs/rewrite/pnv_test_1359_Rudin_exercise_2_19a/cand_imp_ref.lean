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
  refine ⟨⋃ a ∈ A, Metric.ball a (ε / 2), ⋃ b ∈ B, Metric.ball b (ε / 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun a ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  · exact isOpen_iUnion fun b ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  · intro a ha
    simp only [Set.mem_iUnion]
    exact ⟨a, ha, Metric.mem_ball_self (half_pos hε)⟩
  · intro b hb
    simp only [Set.mem_iUnion]
    exact ⟨b, hb, Metric.mem_ball_self (half_pos hε)⟩
  · rw [Set.disjoint_left]
    intro z hzA hzB
    simp only [Set.mem_iUnion, exists_prop, Metric.mem_ball] at hzA hzB
    obtain ⟨a, ha, hza⟩ := hzA
    obtain ⟨b, hb, hzb⟩ := hzB
    have hab : dist a b < ε := by
      rw [dist_comm] at hza
      have := (dist_triangle a z b).trans_lt (add_lt_add hza hzb)
      simpa only [add_halves] using this
    exact (not_lt_of_ge (hdist a ha b hb)) hab
