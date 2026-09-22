import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble has local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem exercise_3_1_assumed {f : ℝ → ℝ}
  (hf : ∀ x y, |f x - f y| ≤ |x - y| ^ 2) :
  ∃ c, f = λ x => c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (h : ∀ t x : ℝ, |f t - f x| ≤ |t - x|^2) : ∃ c : ℝ, f = Function.const ℝ c := by
  simpa [Function.const] using (exercise_3_1_assumed (f := f) h)
