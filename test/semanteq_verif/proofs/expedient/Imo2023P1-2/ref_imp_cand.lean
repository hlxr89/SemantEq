import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

abbrev solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

-- ===== assumed statement (antecedent) =====
theorem imo2023_p1_assumed : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) : 
  n > 1 ∧ ¬Nat.Prime n ∧ 
  ∃ (d : ℕ → ℕ), 
    (∀ i, 0 < d i ∧ d i ∣ n) ∧
    (∀ x, 0 < x ∧ x ∣ n → ∃ i, d i = x) ∧
    (∀ i j, i < j → d i < d j) ∧
    (∀ i, 1 ≤ i ∧ i ≤ (Finset.card (Nat.divisors n) : ℕ) - 2 → d i ∣ d (i + 1) + d (i + 2)) →
  ∃ (p : ℕ) (m : ℕ), Nat.Prime p ∧ m ≥ 2 ∧ n = p ^ m := by
  -- not proved: the candidate statement requires n > 1 for every natural n, so it is false at n = 0
  sorry
