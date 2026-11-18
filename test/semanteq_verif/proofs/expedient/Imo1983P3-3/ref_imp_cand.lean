import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1983_p3_assumed (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  let N := 2 * a * b * c - a * b - b * c - c * a
  (∀ n : ℕ, N < n → ∃ x y z : ℕ, n = x * b * c + y * c * a + z * a * b) ∧
  (¬ ∃ x y z : ℕ, N = x * b * c + y * c * a + z * a * b) := by
  -- not proved: false for a = b = c = 1 because natural subtraction truncates -1 to 0
  sorry
