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
  obtain ⟨n, hn, _⟩ := dummy_assumed (a := 1) (n := 0) (by omega)
  norm_num at hn
  have hle : 1 - 2 ^ n ≤ 1 := Nat.sub_le _ _
  omega

