import Mathlib

-- ===== assumed statement (antecedent) =====
theorem c_assumed : Irrational (Real.sqrt 2) ∧ (2 + 2 = 4) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem r : Irrational (Real.sqrt 2) := by
  exact c_assumed.1
