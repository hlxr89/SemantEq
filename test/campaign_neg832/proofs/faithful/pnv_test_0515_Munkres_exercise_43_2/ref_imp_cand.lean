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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (f : X → Y) (A : Set X) (hA : IsClosed A) (hf : UniformContinuousOn f A) : ∃! g : X → Y, ∀ x ∈ A, g x = f x ∧ Continuous g ∧ UniformContinuous g := by
  have hempty (u : X → Y) : UniformContinuousOn u ∅ := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    exact ⟨1, zero_lt_one, by simp⟩
  rcases exercise_43_2_assumed (∅ : Set X) f (hempty f) with ⟨g₀, hg₀, huniq⟩
  have hall : ∀ u v : X → Y, u = v := by
    intro u v
    have hu : u = g₀ := huniq u ⟨by simp, by simpa only [closure_empty] using hempty u, by simp⟩
    have hv : v = g₀ := huniq v ⟨by simp, by simpa only [closure_empty] using hempty v, by simp⟩
    exact hu.trans hv.symm
  cases isEmpty_or_nonempty X with
  | inl hX =>
      refine ⟨f, ?_, ?_⟩
      · intro x
        exact isEmptyElim x
      · intro g hg
        exact hall g f
  | inr hX =>
      let x₀ : X := Classical.choice hX
      let c : X → Y := fun _ => f x₀
      have hfc : f = c := hall f c
      refine ⟨f, ?_, ?_⟩
      · intro x hx
        refine ⟨rfl, ?_, ?_⟩
        rw [hfc]
        exact continuous_const
        rw [hfc]
        exact uniformContinuous_const
      · intro g hg
        exact hall g f
