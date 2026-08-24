/-
Autoformalized from NL only (blind); benchmark: Compfiles; problem: Imo1974P3.
-/
import Mathlib

/-- Prove that the sum from k = 0 to n inclusive of
   Choose[2n + 1, 2k + 1] * 2³ᵏ
is not divisible by 5 for any integer n ≥ 0. -/
theorem Imo1974P3 (n : ℕ) :
    ¬ (5 ∣ ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * 2 ^ (3 * k)) :=
  sorry
