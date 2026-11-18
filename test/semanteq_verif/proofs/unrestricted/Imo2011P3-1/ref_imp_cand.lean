import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo2011_p3_assumed (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) ≤ y * f x + f (f x)) :
    ∀ x ≤ 0, f x = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∀ (f : ℝ → ℝ), 
  (∀ x y : ℝ, f (x + y) ≤ y * f x + f (f x)) → 
  (∀ x : ℝ, x ≤ 0 → f x = 0) := by
  intro f hf
  exact imo2011_p3_assumed f hf
