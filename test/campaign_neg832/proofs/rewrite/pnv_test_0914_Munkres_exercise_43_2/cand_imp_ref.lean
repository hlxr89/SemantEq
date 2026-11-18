import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {A : Set X} {f : X → Y} (hfc : UniformContinuousOn f A) : ∃! g : X → Y, Continuous g ∧ EqOn f g A ∧ UniformContinuous g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  rcases dummy_assumed hf with ⟨g, hg, -⟩
  cases isEmpty_or_nonempty X with
  | inl hX =>
      refine ⟨g, ⟨hg.1.continuousOn, hg.2.2.uniformContinuousOn, ?_⟩, ?_⟩
      · intro x
        exact isEmptyElim x.1
      · intro k _
        funext x
        exact isEmptyElim x
  | inr hX =>
      have hfempty : UniformContinuousOn f (∅ : Set X) := by
        rw [Metric.uniformContinuousOn_iff]
        intro ε hε
        exact ⟨1, zero_lt_one, fun _ hx => hx.elim⟩
      rcases dummy_assumed hfempty with ⟨u, hu, hu_unique⟩
      letI : Subsingleton Y :=
        ⟨fun a b => by
          let ca : X → Y := fun _ => a
          let cb : X → Y := fun _ => b
          have hca : Continuous ca ∧ EqOn f ca (∅ : Set X) ∧ UniformContinuous ca := by
            exact ⟨continuous_const, fun _ hx => hx.elim, uniformContinuous_const⟩
          have hcb : Continuous cb ∧ EqOn f cb (∅ : Set X) ∧ UniformContinuous cb := by
            exact ⟨continuous_const, fun _ hx => hx.elim, uniformContinuous_const⟩
          obtain ⟨x⟩ := hX
          exact congrFun ((hu_unique ca hca).trans (hu_unique cb hcb).symm) x⟩
      refine ⟨g, ⟨hg.1.continuousOn, hg.2.2.uniformContinuousOn, ?_⟩, ?_⟩
      · intro x
        exact (hg.2.1 x.2).symm
      · intro k _
        funext x
        exact Subsingleton.elim _ _
