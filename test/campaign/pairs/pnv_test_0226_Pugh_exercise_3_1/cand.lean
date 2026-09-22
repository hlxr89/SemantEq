import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {f : ℝ → ℝ} (h : ∀ t x : ℝ, abs (f t - f x) ≤ (abs (t - x))^2) : ∀ x y : ℝ, f x = f y := sorry
