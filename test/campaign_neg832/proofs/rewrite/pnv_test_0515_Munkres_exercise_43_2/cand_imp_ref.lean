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
  have hf_empty : UniformContinuousOn f (∅ : Set X) :=
    hf.mono (empty_subset A)
  obtain ⟨g, hg, huniq⟩ :=
    dummy_assumed f (∅ : Set X) isClosed_empty hf_empty
  have hall : ∀ k : X → Y, k = g := by
    intro k
    apply huniq k
    intro x hx
    exact False.elim hx
  have hg_cont : Continuous g := by
    cases isEmpty_or_nonempty X with
    | inl hX =>
        letI : IsEmpty X := hX
        rw [continuous_iff_continuousAt]
        intro x
        exact isEmptyElim x
    | inr hX =>
        letI : Nonempty X := hX
        let c : X → Y := fun _ => g (Classical.choice hX)
        have hc : Continuous c := continuous_const
        rw [hall c] at hc
        exact hc
  have hg_unif : UniformContinuous g := by
    cases isEmpty_or_nonempty X with
    | inl hX =>
        letI : IsEmpty X := hX
        rw [Metric.uniformContinuous_iff]
        intro ε hε
        refine ⟨1, zero_lt_one, ?_⟩
        intro a b hab
        exact isEmptyElim a
    | inr hX =>
        letI : Nonempty X := hX
        let c : X → Y := fun _ => g (Classical.choice hX)
        have hc : UniformContinuous c := uniformContinuous_const
        rw [hall c] at hc
        exact hc
  refine ⟨g, ?_, ?_⟩
  · refine ⟨hg_cont.continuousOn, hg_unif.uniformContinuousOn, ?_⟩
    intro x
    exact congrFun (hall f).symm x
  · intro k hk
    exact hall k
