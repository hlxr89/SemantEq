import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {f : ℝ → ℝ} : UniformContinuous f ↔ ∃ μ : ℝ → ℝ, StrictMono μ ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧ ∀ s t, |f s - f t| ≤ μ (|s - t|) := sorry
