/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Imo2019P4_refs`, proof replaced by `sorry`.
-/
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic

/-!
# International Mathematical Olympiad 2019, Problem 4

Determine all positive integers n,k that satisfy the equation

  k! = (2ⁿ - 2⁰)(2ⁿ - 2¹) ... (2ⁿ - 2ⁿ⁻¹).
-/

open scoped Nat

def solution_set : Set (ℕ × ℕ) := { (1,1), (2,3) }

theorem Imo2019P4_refs (n k : ℕ) :
    (n, k) ∈ solution_set ↔
    0 < n ∧ 0 < k ∧
    (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2:ℤ)^n - (2:ℤ)^i) := by sorry
