import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty: neither preamble has local definitions or structures

-- ===== assumed statement (antecedent) =====
theorem exercise_43_2_assumed {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {A : Set X} {f : X → Y} (hfc : UniformContinuousOn f A) : ∃! g : X → Y, Continuous g ∧ EqOn f g A ∧ UniformContinuous g := by
  let z : Unit → ℝ := fun _ => 0
  let o : Unit → ℝ := fun _ => 1
  obtain ⟨g, hg, huniq⟩ :=
    exercise_43_2_assumed (∅ : Set Unit) z
      (uniformContinuous_const.uniformContinuousOn)
  have hz : ContinuousOn z (closure (∅ : Set Unit)) ∧
      UniformContinuousOn z (closure (∅ : Set Unit)) ∧
      ∀ (x : (∅ : Set Unit)), z x = z x := by
    constructor
    · exact continuous_const.continuousOn
    constructor
    · exact uniformContinuous_const.uniformContinuousOn
    · intro x
      exact False.elim x.property
  have ho : ContinuousOn o (closure (∅ : Set Unit)) ∧
      UniformContinuousOn o (closure (∅ : Set Unit)) ∧
      ∀ (x : (∅ : Set Unit)), o x = z x := by
    constructor
    · exact continuous_const.continuousOn
    constructor
    · exact uniformContinuous_const.uniformContinuousOn
    · intro x
      exact False.elim x.property
  have hzo : z = o := (huniq z hz).trans (huniq o ho).symm
  have : (0 : ℝ) = 1 := congrFun hzo ()
  norm_num at this

