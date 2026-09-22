/-
Autoformalized from NL only (blind); benchmark: Compfiles; problem: UK2024R1P4.
-/
import Mathlib

/-- The positive integers `n` such that `n * 2 ^ n + 1` is a square: 2 and 3. -/
def UK2024R1P4_solution : Set ℕ := {2, 3}

/-- Find all positive integers n such that n × 2ⁿ + 1 is a square.

The answer is n = 2 and n = 3. -/
theorem UK2024R1P4 (n : ℕ) (hn : 0 < n) :
    IsSquare (n * 2 ^ n + 1) ↔ n ∈ UK2024R1P4_solution := sorry
