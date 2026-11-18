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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) (A : Set X) (f : X → Y) (hf : UniformContinuousOn f A) : ∃ g : X → Y, ContinuousOn g (closure A) ∧ ∀ x ∈ A, g x = f x ∧ UniformContinuousOn g (closure A) := by
  letI := hY
  rcases exercise_43_2_assumed A f hf with ⟨g, hg, _⟩
  exact ⟨g, hg.1, fun x hx => ⟨hg.2.2 ⟨x, hx⟩, hg.2.1⟩⟩
