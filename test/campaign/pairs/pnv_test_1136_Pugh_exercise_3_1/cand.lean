import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {f : ℝ → ℝ} (hf : ∀ t x : ℝ, abs (f t - f x) ≤ abs (t - x) ^ 2) : ∃ c : ℝ, f = const ℝ c := sorry
