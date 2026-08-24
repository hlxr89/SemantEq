import Mathlib
theorem c {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] (f : X → ℝ) (hf : Continuous f) : ∃ x, ∀ y, f y ≤ f x := by sorry