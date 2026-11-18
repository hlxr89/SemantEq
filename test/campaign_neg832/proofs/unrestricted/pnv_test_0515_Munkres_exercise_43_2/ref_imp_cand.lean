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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (f : X → Y) (A : Set X) (hA : IsClosed A) (hf : UniformContinuousOn f A) : ∃! g : X → Y, ∀ x ∈ A, g x = f x ∧ Continuous g ∧ UniformContinuous g := by
  have h := exercise_43_2_assumed
    (X := Unit) (Y := ℝ) (∅ : Set Unit) (fun _ => 0)
      uniformContinuous_const.uniformContinuousOn
  rcases h with ⟨g, hg, huniq⟩
  have hzero :
      ContinuousOn (fun _ : Unit => (0 : ℝ)) (closure (∅ : Set Unit)) ∧
        UniformContinuousOn (fun _ : Unit => (0 : ℝ)) (closure (∅ : Set Unit)) ∧
        ∀ x : (∅ : Set Unit), (fun _ : Unit => (0 : ℝ)) x = (fun _ => 0) x := by
    constructor
    · simp
    constructor
    · simpa using (uniformContinuous_const.uniformContinuousOn :
        UniformContinuousOn (fun _ : Unit => (0 : ℝ)) (∅ : Set Unit))
    · simp
  have hone :
      ContinuousOn (fun _ : Unit => (1 : ℝ)) (closure (∅ : Set Unit)) ∧
        UniformContinuousOn (fun _ : Unit => (1 : ℝ)) (closure (∅ : Set Unit)) ∧
        ∀ x : (∅ : Set Unit), (fun _ : Unit => (1 : ℝ)) x = (fun _ => 0) x := by
    constructor
    · simp
    constructor
    · simpa using (uniformContinuous_const.uniformContinuousOn :
        UniformContinuousOn (fun _ : Unit => (1 : ℝ)) (∅ : Set Unit))
    · simp
  have e0 := huniq (fun _ : Unit => (0 : ℝ)) hzero
  have e1 := huniq (fun _ : Unit => (1 : ℝ)) hone
  have bad : (0 : ℝ) = 1 := congrFun (e0.trans e1.symm) ()
  norm_num at bad

