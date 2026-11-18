import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
  let S := Finset.Icc 1 (2 * p)
  let target_count := (Finset.filter (fun A => A.card = p ∧ (Finset.sum A id) % p = 0) (Finset.powerset S)).card
  target_count = 2 + (Nat.choose (2 * p) p - 2) / p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  change (((Finset.Icc 1 (2 * p)).powersetCard p).filter
    (fun A ↦ p ∣ ∑ x ∈ A, x)).card =
      2 + (Nat.choose (2 * p) p - 2) / p
  rw [← problem_statement_assumed p hp hodd]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powerset,
    Nat.dvd_iff_mod_eq_zero, id_eq, and_assoc]
