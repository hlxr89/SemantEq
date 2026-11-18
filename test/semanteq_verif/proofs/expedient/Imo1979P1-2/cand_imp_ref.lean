import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def S : ℚ := Finset.sum (Finset.range 1319) (fun k => ((-1 : ℚ) ^ k) / (k + 1 : ℚ))

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ S = (p : ℚ) / (q : ℚ) ∧ Nat.gcd p q = 1 ∧ 1979 ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  let x : ℚ := ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)
  have hn : (1979 : ℤ) ∣ x.num := by native_decide
  have hd : IsCoprime (1979 : ℤ) (x.den : ℤ) := by native_decide
  have hcross : p * (x.den : ℤ) = q * x.num := by
    have hx : (p : ℚ) / q = (x.num : ℚ) / x.den := by
      rw [Rat.num_div_den]
      exact h
    field_simp at hx
    exact_mod_cast hx
  apply hd.dvd_of_dvd_mul_right
  rw [hcross]
  exact dvd_mul_of_dvd_right hn q
