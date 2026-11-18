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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f : X → Y} {A : Set X} (h : UniformContinuousOn f A) : ∃ g : X → Y, UniformContinuous g ∧ EqOn f g A ∧ EqOn f g (closure A) := by
  have hempty : UniformContinuousOn (fun _ : Unit => (0 : ℝ)) (∅ : Set Unit) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    exact ⟨1, by positivity, by simp⟩
  obtain ⟨g, hg, huniq⟩ :=
    exercise_43_2_assumed (X := Unit) (Y := ℝ) (∅ : Set Unit)
      (fun _ => 0) hempty
  have hzero : ContinuousOn (fun _ : Unit => (0 : ℝ)) (closure (∅ : Set Unit)) ∧
      UniformContinuousOn (fun _ : Unit => (0 : ℝ)) (closure (∅ : Set Unit)) ∧
      ∀ (x : (∅ : Set Unit)), (fun _ : Unit => (0 : ℝ)) x = (fun _ => 0) x := by
    refine ⟨continuous_const.continuousOn, uniformContinuous_const.uniformContinuousOn, ?_⟩
    simp
  have hone : ContinuousOn (fun _ : Unit => (1 : ℝ)) (closure (∅ : Set Unit)) ∧
      UniformContinuousOn (fun _ : Unit => (1 : ℝ)) (closure (∅ : Set Unit)) ∧
      ∀ (x : (∅ : Set Unit)), (fun _ : Unit => (1 : ℝ)) x = (fun _ => 0) x := by
    refine ⟨continuous_const.continuousOn, uniformContinuous_const.uniformContinuousOn, ?_⟩
    simp
  have heq : (fun _ : Unit => (0 : ℝ)) = fun _ => 1 :=
    (huniq _ hzero).trans (huniq _ hone).symm
  have : (0 : ℝ) = 1 := congrFun heq ()
  exact (zero_ne_one this).elim
