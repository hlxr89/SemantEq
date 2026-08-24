/-
Gold reference statement (verbatim from PutnamBench lean4/src, solution values filled from gold comments);
theorem renamed `putnam_1976_a3_refs`, proof replaced by `sorry`.
-/
import Mathlib

abbrev putnam_1976_a3_solution : Set (ℕ × ℕ × ℕ × ℕ) := {(3, 2, 2, 3), (2, 3, 3, 2)}
/--
Find all integer solutions $(p, r, q, s)$ of the equation $|p^r - q^s| = 1$, where $p$ and $q$ are prime and $r$ and $s$ are greater than $1$.
-/
theorem putnam_1976_a3_refs
: {(p, r, q, s) : ℕ × ℕ × ℕ × ℕ | Nat.Prime p ∧ Nat.Prime q ∧ r > 1 ∧ s > 1 ∧ |(p^r : ℤ) - q^s| = 1} = putnam_1976_a3_solution :=
sorry
