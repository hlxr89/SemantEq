import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (ha_le : a ≤ n + 1) : a ^ (n + 1) - (a + 1) ^ n = 2001 ↔ a = 2001 ∧ n = 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  refine ⟨(13, 2), by norm_num, ?_⟩
  rintro ⟨a, n⟩ ⟨ha, hn, h⟩
  change a ^ (n + 1) - (a + 1) ^ n = 2001 at h
  have heq : a ^ (n + 1) = 2001 + (a + 1) ^ n := by omega

  have hplus_a : a + 1 ≡ 1 [MOD a] := by
    rw [Nat.ModEq]
    simp [Nat.add_mod]
  have hmod_a : (0 : ℕ) ≡ 2002 [MOD a] := by
    calc
      (0 : ℕ) ≡ a ^ (n + 1) [MOD a] := by
        rw [Nat.ModEq]
        simp [Nat.pow_mod, ha.ne', hn.ne']
      _ ≡ 2001 + (a + 1) ^ n [MOD a] := by rw [heq]
      _ ≡ 2002 [MOD a] := by
        simpa using (Nat.ModEq.refl 2001).add (hplus_a.pow n)
  have ha_dvd : a ∣ 2002 := by
    rw [Nat.ModEq] at hmod_a
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod_a.symm

  have hbase : a * a ≡ 1 [MOD a + 1] := by
    rw [Nat.modEq_iff_dvd]
    use (1 : ℤ) - a
    push_cast
    ring
  have heqmod : a ^ (n + 1) ≡ 2001 [MOD a + 1] := by
    rw [Nat.ModEq]
    have hc := congrArg (fun x : ℕ => x % (a + 1)) heq
    simpa [Nat.add_mod, Nat.pow_mod, ha.ne', hn.ne'] using hc
  have hsquare : (1 : ℕ) ≡ 2001 ^ 2 [MOD a + 1] := by
    have hleft := hbase.pow (n + 1)
    have hright := heqmod.mul heqmod
    have hl : (1 : ℕ) ≡ a ^ (n + 1) * a ^ (n + 1) [MOD a + 1] := by
      simpa [mul_pow, pow_two] using hleft.symm
    have hr : a ^ (n + 1) * a ^ (n + 1) ≡ 2001 ^ 2 [MOD a + 1] := by
      simpa [pow_two] using hright
    exact hl.trans hr
  have hb_dvd : a + 1 ∣ 4004000 := by
    have hz : ((a + 1 : ℕ) : ℤ) ∣ (2001 : ℤ) ^ 2 - 1 := hsquare.dvd
    norm_num at hz ⊢
    exact_mod_cast hz

  have hpow : (a + 1) ^ n < a ^ (n + 1) := by omega
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hbernoulli : 1 + (n : ℚ) / a ≤ (1 + 1 / (a : ℚ)) ^ n := by
    convert one_add_mul_le_pow (a := (1 / (a : ℚ))) (by
      have : (0 : ℚ) ≤ 1 / a := by positivity
      linarith) n using 1 <;> ring
  have hratio : (1 + 1 / (a : ℚ)) ^ n < a := by
    rw [show 1 + 1 / (a : ℚ) = (a + 1) / a by field_simp]
    rw [div_pow, div_lt_iff₀ (pow_pos haq n)]
    norm_cast
    simpa [pow_succ, mul_comm] using hpow
  have hbound_q : (n : ℚ) + a < a * a := by
    have hd : (n : ℚ) / a < a - 1 := by linarith
    apply (div_lt_iff₀ haq).mp at hd
    nlinarith
  have hbound : n + a < a * a := by exact_mod_cast hbound_q

  have ha_le : a ≤ 2002 := Nat.le_of_dvd (by norm_num) ha_dvd
  interval_cases a
  all_goals norm_num at ha_dvd
  all_goals norm_num at hb_dvd
  all_goals norm_num at hbound
  all_goals have hn_le : n ≤ 155 := by omega
  all_goals interval_cases n
  all_goals norm_num at h
  all_goals norm_num
