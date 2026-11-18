import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_43_2_assumed {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {A : Set X} {f : X → Y} (hfc : UniformContinuousOn f A) : ∃! g : X → Y, Continuous g ∧ EqOn f g A ∧ UniformContinuous g := by
  obtain ⟨g, hg, huniq⟩ := exercise_43_2_assumed (∅ : Set Unit) (fun _ ↦ (0 : ℝ))
    uniformContinuous_const.uniformContinuousOn
  have hzero : (fun _ : Unit ↦ (0 : ℝ)) = g := huniq _
    ⟨uniformContinuous_const.continuous.continuousOn,
      uniformContinuous_const.uniformContinuousOn, by simp⟩
  have hone : (fun _ : Unit ↦ (1 : ℝ)) = g := huniq _
    ⟨uniformContinuous_const.continuous.continuousOn,
      uniformContinuous_const.uniformContinuousOn, by simp⟩
  have : (0 : ℝ) = 1 := congrFun (hzero.trans hone.symm) ()
  simp at this
