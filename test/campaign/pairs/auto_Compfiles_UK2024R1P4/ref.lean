/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `UK2024R1P4_refs`, proof replaced by `sorry`.
-/
import Mathlib.Tactic

/-!
# British Mathematical Olympiad 2024, Round 1, Problem 4

Find all positive integers n such that n × 2ⁿ + 1 is a square.

The answer is n = 2 and n = 3.

We follow the presentation by the problem author in https://eventuallyalmosteverywhere.wordpress.com/2024/01/10/finitely-many-solutions/, with modifications.
-/

def SolutionSet : Set ℕ := {2, 3}

theorem UK2024R1P4_refs (n : ℕ) (hn : 0 < n) :
    n ∈ SolutionSet ↔ IsSquare (n * 2 ^ n + 1) := by sorry
