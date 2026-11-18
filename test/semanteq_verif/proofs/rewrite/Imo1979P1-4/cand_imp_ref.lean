import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p q : ℕ) (h1 : 0 < p) (h2 : 0 < q) 
    (h3 : (p : ℚ) / q = Finset.sum (Finset.range 1319) (fun k => (-1 : ℚ) ^ k / (k + 1 : ℚ))) : 
    p % 1979 = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  have hp_cast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp.le
  have hq_cast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hp_nat : 0 < p.toNat := by
    apply Int.natCast_pos.mp
    rw [hp_cast]
    exact hp
  have hq_nat : 0 < q.toNat := by
    apply Int.natCast_pos.mp
    rw [hq_cast]
    exact hq
  have hd_nat : 1979 ∣ p.toNat := by
    rw [Nat.dvd_iff_mod_eq_zero]
    apply problem_statement_assumed p.toNat q.toNat hp_nat hq_nat
    rw [← Int.cast_natCast, hp_cast, ← Int.cast_natCast, hq_cast]
    exact h
  rw [← hp_cast]
  exact Int.natCast_dvd_natCast.mpr hd_nat
