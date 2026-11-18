import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

abbrev solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

noncomputable def has_divisor_property (n : ℕ) : Prop :=
  n > 1 ∧ ¬ Nat.Prime n ∧
  ∀ d₁ d₂ d₃ : ℕ,
    d₁ ∣ n ∧ d₂ ∣ n ∧ d₃ ∣ n ∧
    d₁ < d₂ ∧ d₂ < d₃ →
    d₁ ∣ (d₂ + d₃)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) :
  (n > 1 ∧ ¬ Nat.Prime n ∧ has_divisor_property n) ↔
  ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  -- not proved: the candidate assumption classifies a strictly stronger all-divisor-triples property and does not directly transport the reference's consecutive-divisors converse
  sorry
