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
  -- not proved: one divisible existential witness does not imply divisibility for every representation
  sorry
