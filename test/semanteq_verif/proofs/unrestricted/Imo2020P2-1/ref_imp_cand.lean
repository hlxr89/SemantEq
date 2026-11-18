import Mathlib

open Real

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo2020_p2_assumed (a b c d : ℝ) (hd0 : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (h1 : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a b c d : ℝ) 
  (h1 : a ≥ b) (h2 : b ≥ c) (h3 : c ≥ d) (h4 : d > 0)
  (h5 : a + b + c + d = 1) :
  (a + 2 * b + 3 * c + 4 * d) * a^a * b^b * c^c * d^d < 1 := by
  exact imo2020_p2_assumed a b c d h4 h3 h2 h1 h5
