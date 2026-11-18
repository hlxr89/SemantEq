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
  obtain ⟨a, ha, heq, _⟩ := @dummy_assumed 1
  norm_num at heq
  have hle : a + 1 ≤ a ^ 2 := by omega
  have hsum : a ^ 2 = 2001 + (a + 1) := Nat.eq_add_of_sub_eq hle heq
  have hquad : a * a = a + 2002 := by
    simpa [pow_two, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  by_cases h : a ≤ 45
  · have hnonneg : 0 ≤ a * (45 - a) := Nat.zero_le _
    have hmul : a * a ≤ a * 45 := Nat.mul_le_mul_left a h
    omega
  · have h46 : 46 ≤ a := by omega
    have hmul : 46 * a ≤ a * a := Nat.mul_le_mul_right a h46
    omega
