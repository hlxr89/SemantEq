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
  let P := p.toNat
  let Q := q.toNat
  let d := Nat.gcd P Q
  let a := P / d
  let b := Q / d
  have hP : (P : ℤ) = p := by simp [P, Int.toNat_of_nonneg (le_of_lt hp)]
  have hQ : (Q : ℤ) = q := by simp [Q, Int.toNat_of_nonneg (le_of_lt hq)]
  have hPpos : 0 < P := by omega
  have hQpos : 0 < Q := by omega
  have hd : 0 < d := by simp [d, Nat.gcd_pos_of_pos_left _ hPpos]
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hPpos (Nat.gcd_dvd_left P Q)) hd
  have hb : 0 < b := Nat.div_pos (Nat.le_of_dvd hQpos (Nat.gcd_dvd_right P Q)) hd
  have hab : Nat.gcd a b = 1 := by
    exact (Nat.coprime_div_gcd_div_gcd hd).gcd_eq_one
  have hPd : P = a * d := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left P Q)).symm
  have hQd : Q = b * d := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right P Q)).symm
  have hP_rat : (P : ℚ) = (p : ℚ) := by exact_mod_cast hP
  have hQ_rat : (Q : ℚ) = (q : ℚ) := by exact_mod_cast hQ
  have hred : (p : ℚ) / q = (a : ℚ) / b := by
    calc
      (p : ℚ) / q = (P : ℚ) / Q := by rw [hP_rat, hQ_rat]
      _ = (a : ℚ) / b := by
        rw [hPd, hQd]
        push_cast
        field_simp [Nat.ne_of_gt hd, Nat.ne_of_gt hb]
  have hfrac :
      Finset.sum (Finset.range 1319) (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) =
        (a : ℚ) / (b : ℚ) := by
    calc
      Finset.sum (Finset.range 1319)
          (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) =
          ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        push_cast
        ring
      _ = (p : ℚ) / q := h.symm
      _ = (a : ℚ) / b := hred
  have ha_div : 1979 ∣ a := problem_statement_assumed a b ha hb hab hfrac
  have haP : a ∣ P := by
    exact ⟨d, hPd⟩
  have h1979P : 1979 ∣ P := dvd_trans ha_div haP
  rw [← hP]
  exact_mod_cast h1979P
