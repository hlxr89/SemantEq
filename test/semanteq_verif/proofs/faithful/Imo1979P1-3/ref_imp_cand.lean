import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1979_p1_assumed (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∀ (p q : ℕ), p > 0 → q > 0 → Nat.gcd p q = 1 → 
    Finset.sum (Finset.range 1319) (fun k => ((1 : ℚ) / (↑(k + 1) : ℚ)) * ((-1 : ℚ) ^ k)) = (p : ℚ) / (q : ℚ) →
    1979 ∣ p := by
  intro p q hp hq _ h
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hs : ((p : ℤ) : ℚ) / (q : ℤ) =
      ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1) := by
    simpa [div_eq_mul_inv, mul_comm] using h.symm
  have hd : (1979 : ℤ) ∣ (p : ℤ) := imo1979_p1_assumed (p : ℤ) (q : ℤ) hpz hqz hs
  exact_mod_cast hd
