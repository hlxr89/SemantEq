import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_a3_solution : Set (ℕ × ℕ × ℕ × ℕ) := {(3, 2, 2, 3), (2, 3, 3, 2)}

-- ===== assumed statement (antecedent) =====
theorem putnam_1976_a3_refs_assumed
: {(p, r, q, s) : ℕ × ℕ × ℕ × ℕ | Nat.Prime p ∧ Nat.Prime q ∧ r > 1 ∧ s > 1 ∧ |(p^r : ℤ) - q^s| = 1} = putnam_1976_a3_solution :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1976_a3 (p r q s : ℕ) :
    (p.Prime ∧ q.Prime ∧ 1 < r ∧ 1 < s ∧ |(p : ℤ) ^ r - (q : ℤ) ^ s| = 1) ↔
    (p, r, q, s) ∈ putnam_1976_a3_solution := by
  simpa using Set.ext_iff.mp putnam_1976_a3_refs_assumed (p, r, q, s)
