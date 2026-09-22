import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_1_assumed {f : ℝ → ℝ}
  (hf : ∀ x y, |f x - f y| ≤ |x - y| ^ 2) :
  ∃ c, f = λ x => c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (hf : ∀ t x : ℝ, |f t - f x| ≤ |t - x| ^ 2) : ∃ c : ℝ, f = const ℝ c := by
  simpa only [const] using exercise_3_1_assumed hf
