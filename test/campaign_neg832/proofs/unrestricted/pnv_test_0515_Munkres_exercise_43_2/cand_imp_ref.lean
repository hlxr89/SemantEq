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
  have h := dummy_assumed
    (X := Unit) (Y := ℝ) (fun _ => 0) (∅ : Set Unit) (by simp)
      uniformContinuous_const.uniformContinuousOn
  rcases h with ⟨g, hg, huniq⟩
  have hzero :
      ∀ x ∈ (∅ : Set Unit),
        (fun _ : Unit => (0 : ℝ)) x = (fun _ => 0) x ∧
          Continuous (fun _ : Unit => (0 : ℝ)) ∧
          UniformContinuous (fun _ : Unit => (0 : ℝ)) := by
    simp
  have hone :
      ∀ x ∈ (∅ : Set Unit),
        (fun _ : Unit => (1 : ℝ)) x = (fun _ => 0) x ∧
          Continuous (fun _ : Unit => (1 : ℝ)) ∧
          UniformContinuous (fun _ : Unit => (1 : ℝ)) := by
    simp
  have e0 := huniq (fun _ : Unit => (0 : ℝ)) hzero
  have e1 := huniq (fun _ : Unit => (1 : ℝ)) hone
  have bad : (0 : ℝ) = 1 := congrFun (e0.trans e1.symm) ()
  norm_num at bad

