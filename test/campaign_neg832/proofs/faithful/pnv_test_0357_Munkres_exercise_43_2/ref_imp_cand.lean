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
  classical
  letI : CompleteSpace Y := hY
  by_cases hA : A.Nonempty
  · rcases hA with ⟨a, ha⟩
    let F : X → Y := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else f ⟨a, ha⟩
    have hF : UniformContinuousOn F A := by
      rw [Metric.uniformContinuousOn_iff]
      rw [Metric.uniformContinuous_iff] at hf
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := hf ε hε
      refine ⟨δ, hδ, ?_⟩
      intro x hx y hy hxy
      simpa [F, hx, hy] using
        (hbound (a := (⟨x, hx⟩ : A)) (b := (⟨y, hy⟩ : A)) hxy)
    obtain ⟨g, hg, _⟩ := exercise_43_2_assumed A F hF
    refine ⟨fun x => g x, hg.1.restrict, ?_⟩
    rw [Metric.uniformContinuousOn_iff] at hg
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hg.2.1 ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy
    exact hbound x x.property y y.property hxy
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    have hempty (x : closure A) : False := by
      have hx : (x : X) ∈ (∅ : Set X) := by
        simpa [hAe] using x.property
      exact hx
    let g : closure A → Y := fun x => (hempty x).elim
    refine ⟨g, ?_, ?_⟩
    · rw [continuous_iff_continuousAt]
      intro x
      exact (hempty x).elim
    · rw [Metric.uniformContinuous_iff]
      intro ε hε
      refine ⟨1, zero_lt_one, ?_⟩
      intro x
      exact (hempty x).elim
