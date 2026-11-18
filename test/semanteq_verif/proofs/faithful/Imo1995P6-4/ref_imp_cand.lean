import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

-- ===== assumed statement (antecedent) =====
theorem imo1995_p6_assumed (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
  (Finset.filter (fun A => A.card = p ∧ (A.sum id) % p = 0) (Finset.powerset (Finset.Icc 1 (2 * p)))).card = 2 + (Nat.choose (2 * p) p - 2) / p := by
  simpa [solution, Finset.powersetCard_eq_filter, Finset.filter_filter,
    Nat.dvd_iff_mod_eq_zero, and_comm] using imo1995_p6_assumed p hp hp_odd
