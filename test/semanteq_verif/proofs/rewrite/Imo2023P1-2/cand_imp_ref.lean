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
theorem problem_statement_assumed (n : ℕ) : 
  n > 1 ∧ ¬Nat.Prime n ∧ 
  ∃ (d : ℕ → ℕ), 
    (∀ i, 0 < d i ∧ d i ∣ n) ∧
    (∀ x, 0 < x ∧ x ∣ n → ∃ i, d i = x) ∧
    (∀ i j, i < j → d i < d j) ∧
    (∀ i, 1 ≤ i ∧ i ≤ (Finset.card (Nat.divisors n) : ℕ) - 2 → d i ∣ d (i + 1) + d (i + 2)) →
  ∃ (p : ℕ) (m : ℕ), Nat.Prime p ∧ m ≥ 2 ∧ n = p ^ m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  -- not proved: the candidate assumption is inconsistent at n = 0, so only the forbidden ex-falso route is available
  sorry
