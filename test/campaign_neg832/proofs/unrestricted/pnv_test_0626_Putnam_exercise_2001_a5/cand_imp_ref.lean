import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (ha : 0 < a) : ∃! (n : ℕ), 0 < n ∧ a ^ (n + 1) - (a + 1) ^ n = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  obtain ⟨m, hm, _⟩ := dummy_assumed (a := 1) (n := 0) (by norm_num)
  rcases hm with ⟨hm, heq⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  norm_num [pow_succ] at heq
  have hpow : 0 < 2 ^ k * 2 := by positivity
  omega
