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
  dsimp only at ha hn h ⊢
  have heq : a ^ (n + 1) = (a + 1) ^ n + 2001 := by omega
  have heqz : (a : ℤ) ^ (n + 1) - ((a : ℤ) + 1) ^ n = 2001 := by
    have hz : (a : ℤ) ^ (n + 1) = ((a + 1 : ℕ) ^ n : ℤ) + 2001 := by
      exact_mod_cast heq
    push_cast at hz
    omega
  have hbasea : (a : ℤ) + 1 ≡ 1 [ZMOD (a : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    simp
  have hpowa := hbasea.pow n
  have hA : (a : ℤ) ∣ (a : ℤ) ^ (n + 1) := by
    exact dvd_pow_self _ (by omega)
  have hda : (a : ℤ) ∣ 2002 := by
    rcases hA with ⟨x, hx⟩
    rcases hpowa.dvd with ⟨y, hy⟩
    norm_num at hy
    refine ⟨x + y, ?_⟩
    calc
      2002 = (a : ℤ) ^ (n + 1) + (1 - ((a : ℤ) + 1) ^ n) := by omega
      _ = (a : ℤ) * x + (a : ℤ) * y := by rw [hx, hy]
      _ = (a : ℤ) * (x + y) := by ring
  have hbase : (a : ℤ) ≡ -1 [ZMOD (a : ℤ) + 1] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by ring⟩
  have hEqMod : (a : ℤ) ^ (n + 1) ≡ 2001 [ZMOD (a : ℤ) + 1] := by
    rw [Int.modEq_iff_dvd]
    have hdB : (a : ℤ) + 1 ∣ ((a : ℤ) + 1) ^ n := by
      exact dvd_pow_self _ (by omega)
    rcases hdB with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    calc
      2001 - (a : ℤ) ^ (n + 1) = -((a : ℤ) + 1) ^ n := by omega
      _ = ((a : ℤ) + 1) * (-k) := by rw [hk]; ring
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hdm : (a : ℤ) + 1 ∣ 2002 := by
      have hd1 := hEqMod.dvd
      have hd2 := (hbase.pow (n + 1)).dvd
      have hpneg : (-1 : ℤ) ^ (n + 1) = -1 := by
        have hsquare : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
          rw [← pow_add]
          simp
        rw [hk]
        calc
          (-1 : ℤ) ^ (k + k + 1) = ((-1 : ℤ) ^ k * (-1 : ℤ) ^ k) * (-1) := by
            rw [pow_succ, pow_add]
          _ = -1 := by rw [hsquare]; norm_num
      rw [hpneg] at hd2
      rcases hd1 with ⟨x, hx⟩
      rcases hd2 with ⟨y, hy⟩
      refine ⟨x - y, ?_⟩
      calc
        2002 = (2001 - (a : ℤ) ^ (n + 1)) - (-1 - (a : ℤ) ^ (n + 1)) := by ring
        _ = ((a : ℤ) + 1) * x - ((a : ℤ) + 1) * y := by rw [hx, hy]
        _ = ((a : ℤ) + 1) * (x - y) := by ring
    have ha_le : a ≤ 2002 := by
      norm_cast at hda
      exact Nat.le_of_dvd (by norm_num) hda
    have ha_cases : a = 1 ∨ a = 13 := by
      interval_cases a <;> norm_num at hda <;> norm_num at hdm <;> simp_all
    rcases ha_cases with rfl | rfl
    · norm_num at heq
      have hpowpos : 0 < 2 ^ n := pow_pos (by norm_num) _
      omega
    · have hn_lt : n < 35 := by
        by_contra hnot
        have hn35 : 35 ≤ n := by omega
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn35
        have hbasepow : 13 ^ 36 ≤ 14 ^ 35 := by norm_num
        have htpow : 13 ^ t ≤ 14 ^ t := by
          exact Nat.pow_le_pow_left (by norm_num) t
        have hle : 13 ^ (35 + t + 1) ≤ 14 ^ (35 + t) := by
          calc
            13 ^ (35 + t + 1) = 13 ^ 36 * 13 ^ t := by ring_nf
            _ ≤ 14 ^ 35 * 14 ^ t := Nat.mul_le_mul hbasepow htpow
            _ = 14 ^ (35 + t) := by rw [pow_add]
        norm_num at heq
        omega
      interval_cases n <;> norm_num at heq <;> norm_num
  · have hdm : (a : ℤ) + 1 ∣ 2000 := by
      have hd1 := hEqMod.dvd
      have hd2 := (hbase.pow (n + 1)).dvd
      have hpneg : (-1 : ℤ) ^ (n + 1) = 1 := by
        have hsquare : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
          rw [← pow_add]
          simp
        rw [hk]
        calc
          (-1 : ℤ) ^ (2 * k + 1 + 1) = ((-1 : ℤ) ^ k * (-1 : ℤ) ^ k) * (-1) * (-1) := by
            rw [show 2 * k + 1 + 1 = k + k + 1 + 1 by omega, pow_succ, pow_succ, pow_add]
          _ = 1 := by rw [hsquare]; norm_num
      rw [hpneg] at hd2
      rcases hd1 with ⟨x, hx⟩
      rcases hd2 with ⟨y, hy⟩
      refine ⟨x - y, ?_⟩
      calc
        2000 = (2001 - (a : ℤ) ^ (n + 1)) - (1 - (a : ℤ) ^ (n + 1)) := by ring
        _ = ((a : ℤ) + 1) * x - ((a : ℤ) + 1) * y := by rw [hx, hy]
        _ = ((a : ℤ) + 1) * (x - y) := by ring
    have ha_le : a ≤ 2002 := by
      norm_cast at hda
      exact Nat.le_of_dvd (by norm_num) hda
    have ha_cases : a = 1 ∨ a = 7 := by
      interval_cases a <;> norm_num at hda <;> norm_num at hdm <;> simp_all
    rcases ha_cases with rfl | rfl
    · norm_num at heq
      have hpowpos : 0 < 2 ^ n := pow_pos (by norm_num) _
      omega
    · have hn_lt : n < 15 := by
        by_contra hnot
        have hn15 : 15 ≤ n := by omega
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn15
        have hbasepow : 7 ^ 16 ≤ 8 ^ 15 := by norm_num
        have htpow : 7 ^ t ≤ 8 ^ t := by
          exact Nat.pow_le_pow_left (by norm_num) t
        have hle : 7 ^ (15 + t + 1) ≤ 8 ^ (15 + t) := by
          calc
            7 ^ (15 + t + 1) = 7 ^ 16 * 7 ^ t := by ring_nf
            _ ≤ 8 ^ 15 * 8 ^ t := Nat.mul_le_mul hbasepow htpow
            _ = 8 ^ (15 + t) := by rw [pow_add]
        norm_num at heq
        omega
      interval_cases n <;> norm_num at heq
