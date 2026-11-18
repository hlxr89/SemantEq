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
  obtain ⟨g, hg, huniq⟩ := exercise_43_2_assumed A f hfc
  classical
  by_cases hcl : closure A = univ
  · refine ⟨g, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact continuousOn_univ.mp (hcl ▸ hg.1)
      · intro x hx
        exact (hg.2.2 ⟨x, hx⟩).symm
      · exact uniformContinuousOn_univ.mp (hcl ▸ hg.2.1)
    · intro g' hg'
      apply huniq g'
      refine ⟨hg'.1.continuousOn, hg'.2.2.uniformContinuousOn, ?_⟩
      intro x
      exact (hg'.2.1 x.property).symm
  · have hx : ∃ x : X, x ∉ closure A := by
      simpa [Set.eq_univ_iff_forall] using hcl
    obtain ⟨x, hx⟩ := hx
    letI : Subsingleton Y :=
      ⟨by
        intro y z
        let gy : X → Y := Function.update g x y
        let gz : X → Y := Function.update g x z
        have heq_y : EqOn gy g (closure A) := by
          intro a ha
          have hne : a ≠ x := by
            intro hax
            subst a
            exact hx ha
          exact Function.update_of_ne hne y g
        have heq_z : EqOn gz g (closure A) := by
          intro a ha
          have hne : a ≠ x := by
            intro hax
            subst a
            exact hx ha
          exact Function.update_of_ne hne z g
        have hgy : ContinuousOn gy (closure A) ∧
            UniformContinuousOn gy (closure A) ∧ ∀ (a : A), gy a = f a := by
          refine ⟨hg.1.congr heq_y, hg.2.1.congr heq_y.symm, ?_⟩
          intro a
          exact (heq_y (subset_closure a.property)).trans (hg.2.2 a)
        have hgz : ContinuousOn gz (closure A) ∧
            UniformContinuousOn gz (closure A) ∧ ∀ (a : A), gz a = f a := by
          refine ⟨hg.1.congr heq_z, hg.2.1.congr heq_z.symm, ?_⟩
          intro a
          exact (heq_z (subset_closure a.property)).trans (hg.2.2 a)
        have hyz : gy = gz := (huniq gy hgy).trans (huniq gz hgz).symm
        calc
          y = gy x := (Function.update_self x y g).symm
          _ = gz x := congrFun hyz x
          _ = z := Function.update_self x z g⟩
    have hg_cont : Continuous g := by
      rcases isEmpty_or_nonempty X with hX | hX
      · letI := hX
        exact continuous_of_discreteTopology
      · let x₀ := Classical.choice hX
        have heq : g = fun _ => g x₀ := by
          funext a
          exact Subsingleton.elim _ _
        rw [heq]
        exact continuous_const
    have hg_unif : UniformContinuous g := by
      rcases isEmpty_or_nonempty X with hX | hX
      · letI := hX
        rw [Metric.uniformContinuous_iff]
        intro ε hε
        exact ⟨1, zero_lt_one, by intro a; exact isEmptyElim a⟩
      · let x₀ := Classical.choice hX
        have heq : g = fun _ => g x₀ := by
          funext a
          exact Subsingleton.elim _ _
        rw [heq]
        exact uniformContinuous_const
    refine ⟨g, ?_, ?_⟩
    · refine ⟨hg_cont, ?_, hg_unif⟩
      intro x hx
      exact Subsingleton.elim _ _
    · intro g' hg'
      funext x
      exact Subsingleton.elim _ _
