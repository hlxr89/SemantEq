/-
Autoformalized from NL only (blind); benchmark: PutnamBench; problem: putnam_1976_a3.
-/
import Mathlib

/-- The only solutions come from $3^2 - 2^3 = 1$. -/
def putnam_1976_a3_solution : Set (ℕ × ℕ × ℕ × ℕ) :=
  {(3, 2, 2, 3), (2, 3, 3, 2)}

/-- Find all integer solutions $(p, r, q, s)$ of the equation $|p^r - q^s| = 1$, where $p$ and $q$ are prime and $r$ and $s$ are greater than $1$. -/
theorem putnam_1976_a3 (p r q s : ℕ) :
    (p.Prime ∧ q.Prime ∧ 1 < r ∧ 1 < s ∧ |(p : ℤ) ^ r - (q : ℤ) ^ s| = 1) ↔
    (p, r, q, s) ∈ putnam_1976_a3_solution := sorry
