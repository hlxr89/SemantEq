import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℕ} (ha : a > 0) (h : a ^ 2 = 2001): ∃ (a' : ℕ) (n : ℕ), a ^ (n + 1) = Nat.succ a' ^ n ∧ a' > 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  refine ⟨(13, 2), by norm_num, ?_⟩
  rintro ⟨a, n⟩ ⟨ha, hn, hdiff⟩
  change a > 0 at ha
  change n > 0 at hn
  change a ^ (n + 1) - (a + 1) ^ n = 2001 at hdiff
  have heq : a ^ (n + 1) = 2001 + (a + 1) ^ n := by omega
  have heqz : (a : ℤ) ^ (n + 1) = 2001 + (a + 1 : ℤ) ^ n := by exact_mod_cast heq
  have hd : a ∣ 2002 := by
    have hza : (a : ℤ) ≡ 0 [ZMOD (a : ℕ)] := by
      rw [Int.modEq_iff_dvd]
      simp
    have hzone : (a + 1 : ℤ) ≡ 1 [ZMOD (a : ℕ)] := by
      rw [Int.modEq_iff_dvd]
      simp
    have hc : (0 : ℤ) ≡ 2002 [ZMOD (a : ℕ)] := by
      calc
        (0 : ℤ) ≡ (a : ℤ) ^ (n + 1) [ZMOD (a : ℕ)] := (hza.pow (n + 1)).symm
        _ = 2001 + (a + 1 : ℤ) ^ n := heqz
        _ ≡ 2001 + (1 : ℤ) ^ n [ZMOD (a : ℕ)] := (Int.ModEq.refl 2001).add (hzone.pow n)
        _ = 2002 := by simp
    rw [Int.modEq_iff_dvd] at hc
    norm_num at hc
    exact_mod_cast hc
  have hale : a ≤ 2002 := Nat.le_of_dvd (by norm_num) hd
  have hz : (a : ℤ) ≡ (-1 : ℤ) [ZMOD (a + 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd]
    use -1
    push_cast
    ring
  have hpw := hz.pow (n + 1)
  rcases Nat.even_or_odd n with hne | hno
  · obtain ⟨k, rfl⟩ := hne
    have hm : (a + 1 : ℕ) ∣ 2002 := by
      have hb0 : (a + 1 : ℤ) ≡ 0 [ZMOD (a + 1 : ℕ)] := by
        rw [Int.modEq_iff_dvd]
        use -1
        push_cast
        ring
      have hc : (2001 : ℤ) ≡ (-1 : ℤ) [ZMOD (a + 1 : ℕ)] := by
        calc
          (2001 : ℤ) = 2001 + 0 := by ring
          _ ≡ 2001 + (a + 1 : ℤ) ^ (k + k) [ZMOD (a + 1 : ℕ)] :=
            (Int.ModEq.refl 2001).add (by
              calc
                (0 : ℤ) = 0 ^ (k + k) := by rw [zero_pow (by omega)]
                _ ≡ (a + 1 : ℤ) ^ (k + k) [ZMOD (a + 1 : ℕ)] := (hb0.pow (k + k)).symm)
          _ = (a : ℤ) ^ (k + k + 1) := heqz.symm
          _ ≡ (-1 : ℤ) ^ (k + k + 1) [ZMOD (a + 1 : ℕ)] := hpw
          _ = -1 := by
            rw [show k + k + 1 = 2 * k + 1 by omega, pow_add, pow_mul]
            norm_num
      rw [Int.modEq_iff_dvd] at hc
      norm_num at hc ⊢
      exact_mod_cast hc
    have hac : a = 1 ∨ a = 13 := by
      interval_cases a <;> (norm_num at hd <;> norm_num at hm <;> norm_num)
    rcases hac with rfl | rfl
    · norm_num at heq
      have hpowpos : 0 < 2 ^ (k + k) := by positivity
      omega
    · have hp : (14 : ℝ) ^ (k + k) < 13 ^ (k + k + 1) := by
        have hpNat : 14 ^ (k + k) < 13 ^ (k + k + 1) := by
          calc
            14 ^ (k + k) < 2001 + 14 ^ (k + k) := by omega
            _ = 13 ^ (k + k + 1) := heq.symm
        exact_mod_cast hpNat
      have hb := one_add_mul_le_pow (R := ℝ) (a := (1 / 13 : ℝ)) (by norm_num) (k + k)
      have hr : (1 + (1 / 13 : ℝ)) ^ (k + k) = 14 ^ (k + k) / 13 ^ (k + k) := by
        rw [show (1 + (1 / 13 : ℝ)) = 14 / 13 by norm_num, div_pow]
      have hratio : (1 + (1 / 13 : ℝ)) ^ (k + k) < 13 := by
        rw [hr, div_lt_iff₀ (by positivity : (0 : ℝ) < 13 ^ (k + k))]
        rw [pow_succ] at hp
        simpa [mul_comm] using hp
      have hklt : k < 78 := by
        have hkr : (k : ℝ) < 78 := by
          norm_num [Nat.cast_add] at hb
          nlinarith
        exact_mod_cast hkr
      interval_cases k <;> (norm_num at heq <;> norm_num)
  · obtain ⟨k, rfl⟩ := hno
    have hm : (a + 1 : ℕ) ∣ 2000 := by
      have hb0 : (a + 1 : ℤ) ≡ 0 [ZMOD (a + 1 : ℕ)] := by
        rw [Int.modEq_iff_dvd]
        use -1
        push_cast
        ring
      have hc : (2001 : ℤ) ≡ (1 : ℤ) [ZMOD (a + 1 : ℕ)] := by
        calc
          (2001 : ℤ) = 2001 + 0 := by ring
          _ ≡ 2001 + (a + 1 : ℤ) ^ (2 * k + 1) [ZMOD (a + 1 : ℕ)] :=
            (Int.ModEq.refl 2001).add (by simpa using (hb0.pow (2 * k + 1)).symm)
          _ = (a : ℤ) ^ (2 * k + 1 + 1) := heqz.symm
          _ ≡ (-1 : ℤ) ^ (2 * k + 1 + 1) [ZMOD (a + 1 : ℕ)] := hpw
          _ = 1 := by
            rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
            norm_num
      rw [Int.modEq_iff_dvd] at hc
      norm_num at hc ⊢
      exact_mod_cast hc
    have hac : a = 1 ∨ a = 7 := by
      interval_cases a <;> (norm_num at hd <;> norm_num at hm <;> norm_num)
    rcases hac with rfl | rfl
    · norm_num at heq
      have hpowpos : 0 < 2 ^ (2 * k + 1) := by positivity
      have : 2001 < (1 : ℕ) := by
        calc
          2001 < 2001 + 2 ^ (2 * k + 1) := Nat.lt_add_of_pos_right hpowpos
          _ = 1 := heq.symm
      omega
    · have hp : (8 : ℝ) ^ (2 * k + 1) < 7 ^ (2 * k + 1 + 1) := by
        have hpNat : 8 ^ (2 * k + 1) < 7 ^ (2 * k + 1 + 1) := by
          calc
            8 ^ (2 * k + 1) < 2001 + 8 ^ (2 * k + 1) := by omega
            _ = 7 ^ (2 * k + 1 + 1) := heq.symm
        exact_mod_cast hpNat
      have hb := one_add_mul_le_pow (R := ℝ) (a := (1 / 7 : ℝ)) (by norm_num) (2 * k + 1)
      have hr : (1 + (1 / 7 : ℝ)) ^ (2 * k + 1) = 8 ^ (2 * k + 1) / 7 ^ (2 * k + 1) := by
        rw [show (1 + (1 / 7 : ℝ)) = 8 / 7 by norm_num, div_pow]
      have hratio : (1 + (1 / 7 : ℝ)) ^ (2 * k + 1) < 7 := by
        rw [hr, div_lt_iff₀ (by positivity : (0 : ℝ) < 7 ^ (2 * k + 1))]
        let m := 2 * k + 1
        change (8 : ℝ) ^ m < 7 * 7 ^ m
        have hp' : (8 : ℝ) ^ m < 7 ^ (m + 1) := by simpa [m] using hp
        have heqr : (7 : ℝ) ^ (m + 1) = 7 * 7 ^ m := by
          rw [pow_succ]
          ring
        exact lt_of_lt_of_eq hp' heqr
      have hklt : k < 21 := by
        have hkr : (k : ℝ) < 21 := by
          norm_num [Nat.cast_add, Nat.cast_mul] at hb
          nlinarith
        exact_mod_cast hkr
      interval_cases k <;> (norm_num at heq <;> norm_num)
