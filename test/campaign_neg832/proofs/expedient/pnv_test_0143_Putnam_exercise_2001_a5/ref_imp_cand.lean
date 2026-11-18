import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2001_a5_assumed :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (ha_le : a ≤ n + 1) : a ^ (n + 1) - (a + 1) ^ n = 2001 ↔ a = 2001 ∧ n = 2 := by
  constructor
  · intro h
    obtain ⟨p, hp, huniq⟩ := exercise_2001_a5_assumed
    have h13 : (13 : ℕ) > 0 ∧ (2 : ℕ) > 0 ∧
        (13 : ℕ) ^ (2 + 1) - (13 + 1) ^ 2 = 2001 := by norm_num
    have han : (a, n) = (13, 2) :=
      (huniq (a, n) ⟨ha, hn, h⟩).trans (huniq (13, 2) h13).symm
    injection han with ha13 hn2
    omega
  · rintro ⟨rfl, rfl⟩
    omega
