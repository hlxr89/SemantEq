import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (h : a^(n+1) - (a+1)^n = 2001) : ∃ (a' : ℕ) (n' : ℕ), a' > 0 ∧ a' = a ∧ n' = n ∧ ∀ (a'' n''), a'' > 0 → a''^(n'+1) - (a''+1)^(n'') ≠ 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  have h : (13 : ℕ)^(2+1) - (13+1)^2 = 2001 := by norm_num
  obtain ⟨a', n', ha', rfl, rfl, hne⟩ := dummy_assumed h
  exact False.elim ((hne 13 2 (by norm_num)) h)
