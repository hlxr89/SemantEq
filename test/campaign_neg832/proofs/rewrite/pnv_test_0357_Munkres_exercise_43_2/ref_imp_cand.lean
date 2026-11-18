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
  cases isEmpty_or_nonempty Y with
  | inl hYempty =>
      have hA : A = ∅ := by
        ext x
        constructor
        · intro hx
          exact isEmptyElim (f ⟨x, hx⟩)
        · intro hx
          exact False.elim hx
      subst A
      let f₀ : closure (∅ : Set X) → Y := fun x =>
        False.elim (by
          simpa only [closure_empty, Set.mem_empty_iff_false] using x.property)
      have hf₀ : UniformContinuous f₀ := (Metric.uniformContinuous_iff).2 (by
        intro ε hε
        refine ⟨ε, hε, ?_⟩
        intro a b hab
        exact False.elim (by
          simpa only [closure_empty, Set.mem_empty_iff_false] using a.property)) -- non-rewrite step
      obtain ⟨g, hg, huniq⟩ :=
        exercise_43_2_assumed (X := closure (∅ : Set X)) (Y := Y)
          Set.univ f₀ hf₀.uniformContinuousOn
      refine ⟨g, ?_, ?_⟩
      · exact continuousOn_univ.mp (by
          simpa only [closure_univ] using hg.1)
      · exact uniformContinuousOn_univ.mp (by
          simpa only [closure_univ] using hg.2.1)
  | inr hYnonempty =>
      classical
      let y₀ : Y := Classical.choice hYnonempty
      let F : X → Y := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else y₀
      have hrestrict : A.restrict F = f := by
        funext x
        simp only [Set.restrict_apply]
        simp only [F, dif_pos x.property]
      have hF : UniformContinuousOn F A :=
        uniformContinuousOn_iff_restrict.mpr (by
          rw [hrestrict]
          exact hf)
      obtain ⟨g, hg, huniq⟩ := exercise_43_2_assumed A F hF
      exact ⟨(closure A).restrict g,
        continuousOn_iff_continuous_restrict.mp hg.1,
        uniformContinuousOn_iff_restrict.mp hg.2.1⟩
