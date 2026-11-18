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
  rcases exercise_43_2_assumed A f hfc with ⟨g, hg, -⟩
  cases isEmpty_or_nonempty X with
  | inl hX =>
      have hgu : UniformContinuous g := by
        rw [Metric.uniformContinuous_iff]
        intro ε hε
        exact ⟨1, zero_lt_one, fun {_ _} _ => isEmptyElim ‹X›⟩
      refine ⟨g, ⟨hgu.continuous, ?_, hgu⟩, ?_⟩
      · intro x _
        exact isEmptyElim x
      · intro k _
        funext x
        exact isEmptyElim x
  | inr hX =>
      have hfempty : UniformContinuousOn f (∅ : Set X) := by
        rw [Metric.uniformContinuousOn_iff]
        intro ε hε
        exact ⟨1, zero_lt_one, fun _ hx => hx.elim⟩
      rcases exercise_43_2_assumed (∅ : Set X) f hfempty with ⟨u, hu, hu_unique⟩
      letI : Subsingleton Y :=
        ⟨fun a b => by
          let ca : X → Y := fun _ => a
          let cb : X → Y := fun _ => b
          have hca_uc : UniformContinuousOn ca (∅ : Set X) := by
            rw [Metric.uniformContinuousOn_iff]
            intro ε hε
            exact ⟨1, zero_lt_one, fun _ hx => hx.elim⟩
          have hcb_uc : UniformContinuousOn cb (∅ : Set X) := by
            rw [Metric.uniformContinuousOn_iff]
            intro ε hε
            exact ⟨1, zero_lt_one, fun _ hx => hx.elim⟩
          have hca : ContinuousOn ca (closure (∅ : Set X)) ∧
              UniformContinuousOn ca (closure (∅ : Set X)) ∧
              ∀ (x : (∅ : Set X)), ca x = f x := by
            rw [closure_empty]
            exact ⟨continuousOn_empty ca, hca_uc, fun x => x.2.elim⟩
          have hcb : ContinuousOn cb (closure (∅ : Set X)) ∧
              UniformContinuousOn cb (closure (∅ : Set X)) ∧
              ∀ (x : (∅ : Set X)), cb x = f x := by
            rw [closure_empty]
            exact ⟨continuousOn_empty cb, hcb_uc, fun x => x.2.elim⟩
          obtain ⟨x⟩ := hX
          exact congrFun ((hu_unique ca hca).trans (hu_unique cb hcb).symm) x⟩
      have hgu : UniformContinuous g := by
        rw [Metric.uniformContinuous_iff]
        intro ε hε
        exact ⟨1, zero_lt_one, fun {_ _} _ => by
          rw [Subsingleton.elim (g _) (g _), dist_self]
          exact hε⟩
      refine ⟨g, ⟨hgu.continuous, ?_, hgu⟩, ?_⟩
      · intro x hx
        exact (hg.2.2 ⟨x, hx⟩).symm
      · intro k _
        funext x
        exact Subsingleton.elim _ _
