import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (f : X → Y) (A : Set X) (hA : IsClosed A) (hf : UniformContinuousOn f A) : ∃! g : X → Y, ∀ x ∈ A, g x = f x ∧ Continuous g ∧ UniformContinuous g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  have hempty (u : X → Y) : UniformContinuousOn u ∅ := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    exact ⟨1, zero_lt_one, by simp⟩
  rcases dummy_assumed f (∅ : Set X) isClosed_empty (hempty f) with ⟨g₀, hg₀, huniq⟩
  cases isEmpty_or_nonempty X with
  | inl hX =>
      have hAe : A = ∅ := by
        ext x
        exact isEmptyElim x
      refine ⟨g₀, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · simp [hAe]
        · simpa only [hAe, closure_empty] using hempty g₀
        · intro x
          exact isEmptyElim x
      · intro g hg
        funext x
        exact isEmptyElim x
  | inr hX =>
      let x₀ : X := Classical.choice hX
      have hconst : ∀ y : Y, (fun _ : X => y) = g₀ := by
        intro y
        apply huniq
        intro x hx
        simp at hx
      have hY : ∀ y z : Y, y = z := by
        intro y z
        have hy := congrFun (hconst y) x₀
        have hz := congrFun (hconst z) x₀
        exact hy.trans hz.symm
      let c : X → Y := fun _ => f x₀
      have hfc : f = c := funext fun x => hY _ _
      have hcont : Continuous f := by
        rw [hfc]
        exact continuous_const
      have hunif : UniformContinuous f := by
        rw [hfc]
        exact uniformContinuous_const
      refine ⟨f, ⟨hcont.continuousOn, hunif.uniformContinuousOn, fun x => rfl⟩, ?_⟩
      intro g hg
      funext x
      exact hY _ _
