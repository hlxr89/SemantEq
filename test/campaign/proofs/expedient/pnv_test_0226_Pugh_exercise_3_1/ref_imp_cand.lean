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
theorem dummy {f : ℝ → ℝ} (h : ∀ t x : ℝ, abs (f t - f x) ≤ (abs (t - x))^2) : ∀ x y : ℝ, f x = f y := by
  obtain ⟨c, rfl⟩ := exercise_3_1_assumed h
  intro x y
  rfl
