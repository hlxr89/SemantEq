/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Imo1974P3_refs`, proof replaced by `sorry`.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

/-!
# International Mathematical Olympiad 1974, Problem 3

Prove that the sum from k = 0 to n inclusive of
   Choose[2n + 1, 2k + 1] * 2³ᵏ
is not divisible by 5 for any integer n ≥ 0.
-/

theorem Imo1974P3_refs
    (n : ℕ) :
    ¬ 5 ∣ ∑ k ∈ Finset.range (n + 1),
            (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by sorry
