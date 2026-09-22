import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h : ∀ t x, abs (f t - f x) ≤ abs (t - x)^2) : ∃ c : ℝ, f = const ℝ c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_1 {f : ℝ → ℝ}
  (hf : ∀ x y, |f x - f y| ≤ |x - y| ^ 2) :
  ∃ c, f = λ x => c := by
  exact dummy_assumed hf
