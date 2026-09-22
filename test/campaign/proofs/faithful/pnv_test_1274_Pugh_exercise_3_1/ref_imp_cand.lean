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
theorem dummy (f : ℝ → ℝ) (hf : ∀ t x, abs (f t - f x) ≤ abs (t - x) ^ 2) : ∃ c : ℝ, ∀ t, f t = c := by
  obtain ⟨c, hc⟩ := exercise_3_1_assumed hf
  exact ⟨c, fun t => congrFun hc t⟩
