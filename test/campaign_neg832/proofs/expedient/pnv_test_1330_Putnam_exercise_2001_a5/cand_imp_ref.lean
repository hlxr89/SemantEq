import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} : ∃ (a : ℕ) (H : 1 ≤ a), a ^ (n + 1) - (a + 1) ^ n = 2001 ∧ ∀ (a' : ℕ) (H' : 1 ≤ a'), a ^ (n + 1) - (a + 1) ^ n ≠ 2001 → a' ≠ a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  obtain ⟨a, ha, h, -⟩ := @dummy_assumed 1
  norm_num [Nat.pow_two] at h
  have heq : a * a = 2001 + (a + 1) := by omega
  have ha_le : a ≤ 46 := by
    by_contra hn
    have ha47 : 47 ≤ a := by omega
    nlinarith [sq_nonneg (a - 47)]
  interval_cases a <;> norm_num at h
