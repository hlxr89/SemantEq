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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) (A : Set X) (f : A → Y) (hf : UniformContinuous f) : ∃ g : closure A → Y, Continuous g ∧ UniformContinuous g := by
  letI : CompleteSpace Y := hY
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    let F : X → Y := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else f ⟨a, ha⟩
    have hF : UniformContinuousOn F A := by
      rw [uniformContinuousOn_iff_restrict]
      have heq : A.restrict F = f := by
        funext x
        simp [F, Set.restrict]
      rw [heq]
      exact hf
    obtain ⟨g, hg, -⟩ := exercise_43_2_assumed A F hF
    exact ⟨(closure A).restrict g, continuousOn_iff_continuous_restrict.mp hg.1,
      uniformContinuousOn_iff_restrict.mp hg.2.1⟩
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    have hEmpty : ∀ x : closure (∅ : Set X), False := by
      intro x
      simpa using x.property
    let g : closure (∅ : Set X) → Y := fun x => (hEmpty x).elim
    refine ⟨g, Metric.continuous_iff.mpr ?_, Metric.uniformContinuous_iff.mpr ?_⟩
    · intro b
      exact (hEmpty b).elim
    · intro ε hε
      exact ⟨1, zero_lt_one, fun {a} => (hEmpty a).elim⟩
