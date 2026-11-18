import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (f : X → Y) (A : Set X) (hA : IsClosed A) (hf : UniformContinuousOn f A) : ∃! g : X → Y, ∀ x ∈ A, g x = f x ∧ Continuous g ∧ UniformContinuous g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  obtain ⟨_, _, hu⟩ := dummy_assumed (fun _ : Unit ↦ (0 : ℝ)) ∅ (by simp)
    uniformContinuous_const.uniformContinuousOn
  have h0 := hu (fun _ ↦ (0 : ℝ)) (by simp)
  have h1 := hu (fun _ ↦ (1 : ℝ)) (by simp)
  have h := h0.trans h1.symm
  exact (zero_ne_one (congrFun h ())).elim
