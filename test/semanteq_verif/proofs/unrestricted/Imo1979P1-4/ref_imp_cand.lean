import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1979_p1_assumed (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (p q : ℕ) (h1 : 0 < p) (h2 : 0 < q) 
    (h3 : (p : ℚ) / q = Finset.sum (Finset.range 1319) (fun k => (-1 : ℚ) ^ k / (k + 1 : ℚ))) : 
    p % 1979 = 0 := by
  have hd : (1979 : ℤ) ∣ (p : ℤ) := by
    apply imo1979_p1_assumed (p : ℤ) (q : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2)
    simpa only [Finset.sum_filter, Finset.mem_range, Nat.cast_add, Nat.cast_one] using h3
  have : 1979 ∣ p := by exact_mod_cast hd
  exact Nat.dvd_iff_mod_eq_zero.mp this
