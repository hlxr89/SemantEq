import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ (ε : ℝ), ε > 0 → μ ε > 0) ∧ (∀ (ε : ℝ), ε > 0 → ∀ (x y : X), dist x y < μ ε → dist (f x) (f y) < ε) := sorry
