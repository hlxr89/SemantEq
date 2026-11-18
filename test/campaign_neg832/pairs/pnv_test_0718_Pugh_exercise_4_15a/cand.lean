import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) : UniformContinuousOn f (Set.Icc a b) ↔ ∃ (M : ℝ → ℝ), ContinuousOn f (Set.Icc a b) ∧ (∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → abs (x - y) < ε → abs (f x - f y) ≤ M ε) ∧ Tendsto M (𝓝[>] 0) (𝓝 0) := sorry
