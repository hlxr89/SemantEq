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
  let d := Nat.gcd p.natAbs q.natAbs
  have hpa : 0 < p.natAbs := Int.natAbs_pos.mpr (ne_of_gt hp)
  have hqa : 0 < q.natAbs := Int.natAbs_pos.mpr (ne_of_gt hq)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q.natAbs hpa
  have hdpa : d ∣ p.natAbs := Nat.gcd_dvd_left _ _
  have hdqa : d ∣ q.natAbs := Nat.gcd_dvd_right _ _
  have hpd : 0 < p.natAbs / d :=
    Nat.div_pos (Nat.le_of_dvd hpa hdpa) hd
  have hqd : 0 < q.natAbs / d :=
    Nat.div_pos (Nat.le_of_dvd hqa hdqa) hd
  have hcop : Nat.gcd (p.natAbs / d) (q.natAbs / d) = 1 := by
    exact Nat.gcd_div_gcd_div_gcd_of_pos_left hpa
  have hp_cast : ((p.natAbs : ℕ) : ℚ) = (p : ℚ) := by
    norm_cast
    simpa [abs_of_pos hp] using Int.natCast_natAbs p
  have hq_cast : ((q.natAbs : ℕ) : ℚ) = (q : ℚ) := by
    norm_cast
    simpa [abs_of_pos hq] using Int.natCast_natAbs q
  have hratio :
      ((p.natAbs / d : ℕ) : ℚ) / ((q.natAbs / d : ℕ) : ℚ) =
        (p : ℚ) / (q : ℚ) := by
    rw [Nat.cast_div hdpa (by exact_mod_cast hd.ne'),
      Nat.cast_div hdqa (by exact_mod_cast hd.ne'), hp_cast, hq_cast]
    field_simp
  have hsum :
      Finset.sum (Finset.range 1319)
          (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) =
        ((p.natAbs / d : ℕ) : ℚ) / ((q.natAbs / d : ℕ) : ℚ) := by
    calc
      _ = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        simp [div_eq_mul_inv, mul_comm]
      _ = (p : ℚ) / (q : ℚ) := h.symm
      _ = _ := hratio.symm
  have hdiv_reduced : 1979 ∣ p.natAbs / d :=
    problem_statement_assumed (p.natAbs / d) (q.natAbs / d) hpd hqd hcop hsum
  have hdiv_nat : 1979 ∣ p.natAbs :=
    hdiv_reduced.trans ⟨d, (Nat.div_mul_cancel hdpa).symm⟩
  have hdiv_int : (1979 : ℤ) ∣ (p.natAbs : ℤ) := by exact_mod_cast hdiv_nat
  simpa [Int.natAbs_of_nonneg hp.le] using hdiv_int
