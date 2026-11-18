import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution (p : ℕ) : ℕ := 2 + (Nat.choose (2 * p) p - 2) / p

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
  (Finset.filter (fun A => A.card = p ∧ (A.sum id) % p = 0) (Finset.powerset (Finset.Icc 1 (2 * p)))).card = 2 + (Nat.choose (2 * p) p - 2) / p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  have hsets :
      ((Finset.Icc 1 (2 * p)).powersetCard p).filter
          (fun A ↦ p ∣ ∑ x ∈ A, x) =
        (Finset.powerset (Finset.Icc 1 (2 * p))).filter
          (fun A ↦ A.card = p ∧ (A.sum id) % p = 0) := by
    ext A
    simp [Nat.dvd_iff_mod_eq_zero, and_assoc, and_left_comm, and_comm]
  rw [hsets]
  simpa [solution] using problem_statement_assumed p hp hodd
