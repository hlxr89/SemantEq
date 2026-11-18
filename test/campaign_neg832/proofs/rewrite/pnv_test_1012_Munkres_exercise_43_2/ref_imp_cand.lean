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
  have hsub : Subsingleton Y :=
    ⟨by
      intro y₁ y₂
      have hempty : UniformContinuousOn (fun _ : Unit => y₁) (∅ : Set Unit) :=
        uniformContinuous_const.uniformContinuousOn
      obtain ⟨g, _, huniq⟩ :=
        exercise_43_2_assumed (Y := Y) (∅ : Set Unit) (fun _ => y₁) hempty
      have hy₁ := huniq (fun _ : Unit => y₁) (by
        refine ⟨?_, ?_, ?_⟩
        · simpa only [closure_empty] using
            (continuous_const.continuousOn : ContinuousOn (fun _ : Unit => y₁) ∅)
        · simpa only [closure_empty] using
            (uniformContinuous_const.uniformContinuousOn :
              UniformContinuousOn (fun _ : Unit => y₁) ∅)
        · intro x
          exact False.elim x.property)
      have hy₂ := huniq (fun _ : Unit => y₂) (by
        refine ⟨?_, ?_, ?_⟩
        · simpa only [closure_empty] using
            (continuous_const.continuousOn : ContinuousOn (fun _ : Unit => y₂) ∅)
        · simpa only [closure_empty] using
            (uniformContinuous_const.uniformContinuousOn :
              UniformContinuousOn (fun _ : Unit => y₂) ∅)
        · intro x
          exact False.elim x.property)
      exact congrFun (hy₁.trans hy₂.symm) ()⟩
  letI : Subsingleton Y := hsub
  obtain ⟨g, ⟨_, _, hgf⟩, _⟩ := exercise_43_2_assumed A f h
  have hg_uniform : UniformContinuous g := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro a b _
    rw [Subsingleton.elim (g a) (g b), dist_self]
    exact hε
  exact ⟨g, hg_uniform, fun x hx => (hgf ⟨x, hx⟩).symm,
    fun x _ => Subsingleton.elim (f x) (g x)⟩
