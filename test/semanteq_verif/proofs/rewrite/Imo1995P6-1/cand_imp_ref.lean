import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  (Finset.filter (fun A => A.card = p ∧ p ∣ A.sum id) (Finset.powerset (Finset.Icc 1 (2 * p)))).card = 2 + (Nat.choose (2 * p) p - 2) / p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  simpa only [solution, Finset.powersetCard_eq_filter, Finset.filter_filter] using
    problem_statement_assumed p hp hodd
