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
  have hp_cast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (le_of_lt hp)
  have hq_cast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (le_of_lt hq)
  have hpN : 0 < p.toNat := by omega
  have hqN : 0 < q.toNat := by omega
  have hpQ : ((p.toNat : ℕ) : ℚ) = (p : ℚ) := by exact_mod_cast hp_cast
  have hqQ : ((q.toNat : ℕ) : ℚ) = (q : ℚ) := by exact_mod_cast hq_cast
  have hsum : ((p.toNat : ℕ) : ℚ) / q.toNat =
      Finset.sum (Finset.range 1319) (fun k => (-1 : ℚ) ^ k / (k + 1 : ℚ)) := by
    rw [hpQ, hqQ]
    simpa using h
  have hmod : p.toNat % 1979 = 0 :=
    problem_statement_assumed p.toNat q.toNat hpN hqN hsum
  have hdvdN : 1979 ∣ p.toNat := Nat.dvd_of_mod_eq_zero hmod
  rw [← hp_cast]
  exact_mod_cast hdvdN
