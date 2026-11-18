import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) : (UniformContinuousOn f (Set.Icc a b)) ↔ ∃ μ : ℝ → ℝ, μ =O[atTop] (fun x => x) ∧ ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → |f t - f s| ≤ μ (|t - s|) := sorry
