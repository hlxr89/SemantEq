import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f : X → Y} {A : Set X} (h : UniformContinuousOn f A) : ∃ g : X → Y, UniformContinuous g ∧ EqOn f g A ∧ EqOn f g (closure A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  exfalso
  have huc : UniformContinuousOn (fun x : ℝ => if x = 0 then (0 : ℕ) else 1) ({0, 1} : Set ℝ) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro x hx y hy hxy
    simp only [mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals norm_num at hxy
    all_goals simpa using hε
  obtain ⟨g, hg, hfg, _⟩ :=
    dummy_assumed (X := ℝ) (Y := ℕ)
      (f := fun x : ℝ => if x = 0 then (0 : ℕ) else 1) (A := {0, 1}) huc
  have heq : g 0 = g 1 :=
    TotallyDisconnectedSpace.eq_of_continuous g hg.continuous 0 1
  have h0 := hfg (show (0 : ℝ) ∈ ({0, 1} : Set ℝ) by simp)
  have h1 := hfg (show (1 : ℝ) ∈ ({0, 1} : Set ℝ) by simp)
  simp at h0 h1
  rw [← h0, ← h1] at heq
  contradiction
