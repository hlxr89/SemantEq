import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ 
  (p : ℚ) / q = Finset.sum (Finset.range 1319) (fun k => ((-1 : ℚ)^k * (1 : ℚ) / (k + 1 : ℚ))) ∧
  1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  let r : ℚ := ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)
  have hn : (1979 : ℤ) ∣ r.num := by native_decide
  have hc : IsCoprime (1979 : ℤ) (r.den : ℤ) := by native_decide
  have hcross : p * (r.den : ℤ) = r.num * q := by
    apply Rat.intCast_inj.mp
    simpa only [Int.cast_mul, Int.cast_natCast] using
      (div_eq_div_iff (show (q : ℚ) ≠ 0 by exact_mod_cast ne_of_gt hq)
        (show (r.den : ℚ) ≠ 0 by exact_mod_cast r.den_nz)).mp
        (show (p : ℚ) / q = (r.num : ℚ) / r.den by
          rw [Rat.num_div_den]
          exact h)
  apply hc.dvd_of_dvd_mul_right
  rw [hcross]
  exact dvd_mul_of_dvd_left hn q
