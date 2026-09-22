/-
Autoformalized from NL only (blind); benchmark: Compfiles; problem: Imo2005P4.
-/
import Mathlib

/-- The set of positive integers relatively prime to every term of the sequence:
only 1. -/
def Imo2005P4_solution : Set ℕ := {1}

/-- Determine all positive integers relatively prime to all the terms of the
infinite sequence `a n = 2 ^ n + 3 ^ n + 6 ^ n - 1`, for `n ≥ 1`. -/
theorem Imo2005P4 (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n → Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1)) ↔
      k ∈ Imo2005P4_solution := sorry
