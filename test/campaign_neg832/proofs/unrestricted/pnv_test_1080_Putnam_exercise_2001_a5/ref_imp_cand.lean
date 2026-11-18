import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2001_a5_assumed :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a : ℕ} (ha : a > 0) (h : a ^ 2 = 2001): ∃ (a' : ℕ) (n : ℕ), a ^ (n + 1) = Nat.succ a' ^ n ∧ a' > 0 := by
  have ha_cases : a ≤ 44 ∨ 45 ≤ a := by omega
  rcases ha_cases with ha44 | ha45
  · have : a ^ 2 ≤ 44 ^ 2 := Nat.pow_le_pow_left ha44 2
    norm_num [h] at this
  · have : 45 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha45 2
    norm_num [h] at this
