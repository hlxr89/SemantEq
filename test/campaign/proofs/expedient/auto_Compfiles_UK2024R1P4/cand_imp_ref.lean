import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def SolutionSet : Set ℕ := {2, 3}

/-- The positive integers `n` such that `n * 2 ^ n + 1` is a square: 2 and 3. -/
def UK2024R1P4_solution : Set ℕ := {2, 3}

-- ===== assumed statement (antecedent) =====
/-- Find all positive integers n such that n × 2ⁿ + 1 is a square.

The answer is n = 2 and n = 3. -/
theorem UK2024R1P4_assumed (n : ℕ) (hn : 0 < n) :
    IsSquare (n * 2 ^ n + 1) ↔ n ∈ UK2024R1P4_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem UK2024R1P4_refs (n : ℕ) (hn : 0 < n) :
    n ∈ SolutionSet ↔ IsSquare (n * 2 ^ n + 1) := by
  simpa [SolutionSet, UK2024R1P4_solution] using
    (UK2024R1P4_assumed n hn).symm
