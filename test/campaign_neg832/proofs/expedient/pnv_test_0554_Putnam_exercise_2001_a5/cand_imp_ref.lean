import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (h : a^(n+1) - (a+1)^n = 2001) : ∃! (a : ℕ), ∃ (n : ℕ), a^(n+1) - (a+1)^n = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  obtain ⟨x, hx, huniq⟩ := dummy_assumed (a := 13) (n := 2) (by norm_num)
  have h13 : ∃ n : ℕ, 13^(n+1) - (13+1)^n = 2001 := ⟨2, by norm_num⟩
  have h2002 : ∃ n : ℕ, 2002^(n+1) - (2002+1)^n = 2001 := ⟨0, by norm_num⟩
  have h13x : 13 = x := huniq 13 h13
  have h2002x : 2002 = x := huniq 2002 h2002
  omega
