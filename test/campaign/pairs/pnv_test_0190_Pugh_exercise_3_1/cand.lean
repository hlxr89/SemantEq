import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {f : ℝ → ℝ} (h : ∀ t x, abs (f t - f x) ≤ abs (t - x)^2) : ∃ c : ℝ, f = const ℝ c := sorry
