import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy [CompleteSpace ℝ] (f : ℝ → ℝ) (hf : ∀ (t x : ℝ), |f t - f x| ≤ |t - x|^2) : ∃ c : ℝ, ∀ (x : ℝ), f x = c := sorry
