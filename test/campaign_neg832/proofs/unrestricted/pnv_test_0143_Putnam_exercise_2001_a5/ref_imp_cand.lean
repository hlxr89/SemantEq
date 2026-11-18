import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_2001_a5_assumed :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (ha_le : a ≤ n + 1) : a ^ (n + 1) - (a + 1) ^ n = 2001 ↔ a = 2001 ∧ n = 2 := by
  obtain ⟨p, hp, huniq⟩ := exercise_2001_a5_assumed
  have h13 : (13 : ℕ) ^ (2 + 1) - (13 + 1) ^ 2 = 2001 := by norm_num
  have hp13 : p = (13, 2) := (huniq (13, 2) (by norm_num [h13])).symm
  constructor
  · intro h
    have han : (a, n) = (13, 2) := (huniq (a, n) ⟨ha, hn, h⟩).trans hp13
    have ha13 : a = 13 := congrArg Prod.fst han
    have hn2 : n = 2 := congrArg Prod.snd han
    simp at ha13 hn2
    omega
  · rintro ⟨rfl, rfl⟩
    omega
