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
  have hp' : 0 < p.toNat := by omega
  have hq' : 0 < q.toNat := by omega
  have hcastp : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (le_of_lt hp)
  have hcastq : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (le_of_lt hq)
  have hratp : (p.toNat : ℚ) = p := by exact_mod_cast hcastp
  have hratq : (q.toNat : ℚ) = q := by exact_mod_cast hcastq
  have hm : p.toNat % 1979 = 0 := by
    apply problem_statement_assumed p.toNat q.toNat hp' hq'
    simpa only [hratp, hratq, Finset.sum_filter, Finset.mem_range, Nat.cast_add,
      Nat.cast_one] using h
  have hd : 1979 ∣ p.toNat := Nat.dvd_iff_mod_eq_zero.mpr hm
  have hd' : (1979 : ℤ) ∣ (p.toNat : ℤ) := by exact_mod_cast hd
  simpa only [hcastp] using hd'
