import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {a b : ℝ} (f : ℝ → ℝ) : UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ (s t : ℝ), a ≤ s ∧ s ≤ b ∧ a ≤ t ∧ t ≤ b → abs (f s - f t) ≤ μ (abs (s - t))) ∧ Continuous μ ∧ (∀ x > 0, μ x > 0) ∧ (∀ ε > 0, ∃ δ > 0, ∀ s < δ, μ s < ε) := sorry
