import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∀ (p q : ℕ), p > 0 → q > 0 → Nat.gcd p q = 1 → 
    Finset.sum (Finset.range 1319) (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) = (p : ℚ) / (q : ℚ) →
    1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  have hpN : 0 < p.toNat := by
    apply Int.natCast_pos.mp
    rw [Int.toNat_of_nonneg hp.le]
    exact hp
  have hqN : 0 < q.toNat := by
    apply Int.natCast_pos.mp
    rw [Int.toNat_of_nonneg hq.le]
    exact hq
  have hd : 0 < Nat.gcd p.toNat q.toNat :=
    Nat.gcd_pos_of_pos_left q.toNat hpN
  have hc : 1979 ∣ p.toNat / Nat.gcd p.toNat q.toNat := by
    apply problem_statement_assumed
    · exact Nat.div_pos
        (Nat.le_of_dvd hpN (Nat.gcd_dvd_left p.toNat q.toNat)) hd
    · exact Nat.div_pos
        (Nat.le_of_dvd hqN (Nat.gcd_dvd_right p.toNat q.toNat)) hd
    · rw [Nat.gcd_div (Nat.gcd_dvd_left p.toNat q.toNat)
          (Nat.gcd_dvd_right p.toNat q.toNat), Nat.div_self hd]
    · have hsum :
          Finset.sum (Finset.range 1319)
              (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) =
            ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [one_div, inv_mul_eq_div, Nat.cast_add, Nat.cast_one]
      rw [hsum, ← h]
      rw [Nat.cast_div (Nat.gcd_dvd_left p.toNat q.toNat) (by exact_mod_cast hd.ne'),
        Nat.cast_div (Nat.gcd_dvd_right p.toNat q.toNat) (by exact_mod_cast hd.ne'),
        div_div_div_cancel_right₀ (by exact_mod_cast hd.ne')]
      have hpQ : (p.toNat : ℚ) = (p : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hp.le
      have hqQ : (q.toNat : ℚ) = (q : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hq.le
      rw [hpQ, hqQ]
  have hpdiv : 1979 ∣ p.toNat :=
    dvd_trans hc (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left p.toNat q.toNat))
  have hpdivZ : (1979 : ℤ) ∣ (p.toNat : ℤ) := by
    exact_mod_cast hpdiv
  rw [Int.toNat_of_nonneg hp.le] at hpdivZ
  exact hpdivZ
