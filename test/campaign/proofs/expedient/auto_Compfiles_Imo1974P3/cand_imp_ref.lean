import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Imo1974P3_assumed (n : ℕ) :
    ¬ (5 ∣ ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * 2 ^ (3 * k)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo1974P3_refs
    (n : ℕ) :
    ¬ 5 ∣ ∑ k ∈ Finset.range (n + 1),
            (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by
  exact Imo1974P3_assumed n
