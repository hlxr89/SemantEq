import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {f : ℝ → ℝ} : (Continuous f ∧ ∃ μ : ℝ → ℝ, (∀ s : ℝ, 0 < s → μ s > 0) ∧ (∀ s : ℝ, s > 0 → μ s < μ 0) ∧ (∀ s t : ℝ, |f s - f t| ≤ μ (|s - t|))) ↔ UniformContinuous f := sorry
