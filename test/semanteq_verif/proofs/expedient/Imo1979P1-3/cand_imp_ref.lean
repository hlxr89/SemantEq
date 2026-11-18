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
  let pn := p.natAbs
  let qn := q.natAbs
  let d := Nat.gcd pn qn
  have hpn : 0 < pn := by simp [pn, Int.natAbs_pos, ne_of_gt hp]
  have hqn : 0 < qn := by simp [qn, Int.natAbs_pos, ne_of_gt hq]
  have hd : 0 < d := Nat.gcd_pos_of_pos_left qn hpn
  have hcop : Nat.gcd (pn / d) (qn / d) = 1 := by
    exact (Nat.coprime_div_gcd_div_gcd hd).gcd_eq_one
  have hratio :
      Finset.sum (Finset.range 1319) (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) =
        ((pn / d : ℕ) : ℚ) / ((qn / d : ℕ) : ℚ) := by
    have hsum :
        Finset.sum (Finset.range 1319) (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) =
          (pn : ℚ) / (qn : ℚ) := by
      have hpcast : (pn : ℚ) = (p : ℚ) := by
        have hpint : (pn : ℤ) = p := by
          simpa [pn] using Int.natAbs_of_nonneg (le_of_lt hp)
        exact_mod_cast hpint
      have hqcast : (qn : ℚ) = (q : ℚ) := by
        have hqint : (qn : ℤ) = q := by
          simpa [qn] using Int.natAbs_of_nonneg (le_of_lt hq)
        exact_mod_cast hqint
      rw [hpcast, hqcast]
      simpa [div_eq_mul_inv, mul_comm] using h.symm
    rw [hsum, Nat.cast_div (Nat.gcd_dvd_left pn qn) (by exact_mod_cast (ne_of_gt hd)),
      Nat.cast_div (Nat.gcd_dvd_right pn qn) (by exact_mod_cast (ne_of_gt hd))]
    exact (div_div_div_cancel_right₀ (by exact_mod_cast (ne_of_gt hd)) (pn : ℚ) (qn : ℚ)).symm
  have hdiv : 1979 ∣ pn / d := problem_statement_assumed (pn / d) (qn / d)
    (Nat.div_pos (Nat.le_of_dvd hpn (Nat.gcd_dvd_left pn qn)) hd)
    (Nat.div_pos (Nat.le_of_dvd hqn (Nat.gcd_dvd_right pn qn)) hd)
    hcop hratio
  have hmul : pn / d * d = pn := Nat.div_mul_cancel (Nat.gcd_dvd_left pn qn)
  have : 1979 ∣ pn := by
    rw [← hmul]
    exact dvd_mul_of_dvd_left hdiv d
  apply Int.natAbs_dvd_natAbs.mp
  simpa [pn] using this
