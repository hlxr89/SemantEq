import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∀ (f : ℝ → ℝ), 
  (∀ x y : ℝ, f (x + y) ≤ y * f x + f (f x)) → 
  (∀ x : ℝ, x ≤ 0 → f x = 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2011_p3 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) ≤ y * f x + f (f x)) :
    ∀ x ≤ 0, f x = 0 := by
  exact problem_statement_assumed f hf
