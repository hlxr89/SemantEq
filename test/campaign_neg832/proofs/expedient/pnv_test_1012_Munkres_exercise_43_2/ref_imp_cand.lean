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
  exfalso
  obtain ⟨g, _, hg⟩ :=
    exercise_43_2_assumed (X := ℕ) (Y := ℕ) (∅ : Set ℕ)
      (fun _ => 0) uniformContinuous_const.uniformContinuousOn
  have hfalse : (fun _ : ℕ => 0) = g := hg _ (by
    exact ⟨continuous_const.continuousOn,
      uniformContinuous_const.uniformContinuousOn, by simp⟩)
  have htrue : (fun _ : ℕ => 1) = g := hg _ (by
    exact ⟨continuous_const.continuousOn,
      uniformContinuous_const.uniformContinuousOn, by simp⟩)
  have := congrFun (hfalse.trans htrue.symm) 0
  simp at this
