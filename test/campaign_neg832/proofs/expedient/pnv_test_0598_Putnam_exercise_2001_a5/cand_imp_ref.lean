import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ a n : ℕ, 0 < a ∧ 0 < n ∧ a^(n+1) - (a+1)^n = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  refine ⟨(13, 2), by norm_num, ?_⟩
  rintro ⟨a, n⟩ ⟨ha, hn, h⟩
  change 0 < a at ha
  change 0 < n at hn
  change a ^ (n + 1) - (a + 1) ^ n = 2001 at h
  by_cases haeq : a = 1
  · subst a
    have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    norm_num [Nat.sub_eq_zero_of_le hp] at h
  have ha1 : 1 < a := by omega
  have heq : (a + 1) ^ n + 2001 = a ^ (n + 1) := by omega
  have hmod := congrArg (fun x : ℕ => x % a) heq
  simp [Nat.add_mod, Nat.pow_mod, Nat.mod_eq_of_lt ha1] at hmod
  have hdvd : a ∣ 2002 := by
    rw [Nat.dvd_iff_mod_eq_zero, show 2002 = 1 + 2001 by norm_num, Nat.add_mod]
    rw [Nat.mod_eq_of_lt ha1]
    simpa only [Nat.mod_mod_of_dvd _ (dvd_refl a), Nat.mod_eq_of_lt ha1] using hmod
  have hale : a ≤ 2002 := Nat.le_of_dvd (by norm_num) hdvd
  have hc : Nat.ModEq (a + 1) 2001 (a ^ (n + 1)) := by
    show 2001 % (a + 1) = a ^ (n + 1) % (a + 1)
    rw [← heq]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Nat.add_mod]
  have hc2 : Nat.ModEq (a + 1) (2001 ^ 2) ((a ^ 2) ^ (n + 1)) := by
    simpa only [pow_two, ← mul_pow] using hc.mul hc
  interval_cases a <;> norm_num at hdvd
  all_goals norm_num [Nat.ModEq, Nat.pow_mod] at hc2
  · have hnlt : n < 35 := by
      by_contra hnnot
      have hn35 : 35 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn35
      have hp : 7 ^ (35 + k + 1) ≤ 8 ^ (35 + k) := by
        simp only [show 35 + k + 1 = 36 + k by omega, pow_add]
        exact Nat.mul_le_mul (by norm_num) (by gcongr <;> norm_num)
      norm_num at h
      rw [Nat.sub_eq_zero_of_le hp] at h
      norm_num at h
    interval_cases n <;> norm_num at h
  ·
    have hnlt : n < 35 := by
      by_contra hnnot
      have hn35 : 35 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn35
      have hp : 13 ^ (35 + k + 1) ≤ 14 ^ (35 + k) := by
        simp only [show 35 + k + 1 = 36 + k by omega, pow_add]
        exact Nat.mul_le_mul (by norm_num) (by gcongr <;> norm_num)
      norm_num at h
      rw [Nat.sub_eq_zero_of_le hp] at h
      norm_num at h
    interval_cases n <;> norm_num at h
    rfl
