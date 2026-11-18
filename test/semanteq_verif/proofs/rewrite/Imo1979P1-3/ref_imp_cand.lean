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
  have hz : (1979 : ℤ) ∣ (p : ℤ) := by
    apply imo1979_p1_assumed (p : ℤ) (q : ℤ)
    · exact_mod_cast hp
    · exact_mod_cast hq
    · change (p : ℚ) / (q : ℚ) = _
      rw [← h]
      apply Finset.sum_congr rfl
      intro i hi
      rw [one_div, inv_mul_eq_div]
      rw [Nat.cast_add, Nat.cast_one]
  exact_mod_cast hz
