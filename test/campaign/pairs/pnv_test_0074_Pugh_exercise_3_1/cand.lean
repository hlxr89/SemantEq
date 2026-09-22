import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {f : ℝ → ℝ} (h : ∀ t x : ℝ, |f t - f x| ≤ |t - x|^2) : ∃ c : ℝ, f = Function.const ℝ c := sorry
