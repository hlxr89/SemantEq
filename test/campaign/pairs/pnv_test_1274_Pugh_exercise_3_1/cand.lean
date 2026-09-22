import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy (f : ℝ → ℝ) (hf : ∀ t x, abs (f t - f x) ≤ abs (t - x) ^ 2) : ∃ c : ℝ, ∀ t, f t = c := sorry
