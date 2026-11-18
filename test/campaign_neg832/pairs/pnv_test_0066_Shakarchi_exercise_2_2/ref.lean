import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem exercise_2_2 :
  Tendsto (λ y => ∫ x in (0 : ℝ)..y, Real.sin x / x) atTop (𝓝 (Real.pi / 2)) := sorry
