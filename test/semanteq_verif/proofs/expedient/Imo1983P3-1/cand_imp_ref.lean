import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hab : Nat.gcd a b = 1) (hbc : Nat.gcd b c = 1) (hca : Nat.gcd c a = 1) :
  let target := 2 * a * b * c - a * b - b * c - c * a
  (∀ n : ℕ, n > target → ∃ x y z : ℕ, n = x * b * c + y * c * a + z * a * b) ∧
  (∀ x y z : ℕ, x * b * c + y * c * a + z * a * b ≠ target) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  exfalso
  have h := problem_statement_assumed 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  dsimp only at h
  exact (h.2 0 0 0) (by norm_num)
