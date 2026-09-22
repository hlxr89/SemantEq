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
theorem dummy [CompleteSpace ℝ] (f : ℝ → ℝ) (hf : ∀ (t x : ℝ), |f t - f x| ≤ |t - x|^2) : ∃ c : ℝ, ∀ (x : ℝ), f x = c := by
  obtain ⟨c, hc⟩ := exercise_3_1_assumed hf
  exact ⟨c, fun x => congrFun hc x⟩
