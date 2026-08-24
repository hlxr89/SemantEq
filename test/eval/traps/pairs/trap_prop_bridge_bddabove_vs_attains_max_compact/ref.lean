import Mathlib
theorem r {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] (f : X → ℝ) (hf : Continuous f) : BddAbove (Set.range f) := by sorry