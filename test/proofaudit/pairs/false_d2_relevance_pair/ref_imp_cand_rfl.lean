import Mathlib

-- ===== assumed statement (antecedent) =====
theorem r_assumed : Irrational (Real.sqrt 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem c : Irrational (Real.sqrt 2) ∧ (2 + 2 = 4) := by
  exact ⟨r_assumed, rfl⟩
