/-
Benchmark: Compfiles (dwrensha/compfiles, Apache 2.0)
Problem: Imo2001P4
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.Perm.Fin

/-!
# International Mathematical Olympiad 2001, Problem 4

Let $n > 1$ be an odd integer and let $c_1, c_2, \dots, c_n$ be integers. For
each permutation $a = (a_1, a_2, \dots, a_n)$ of $\{1, 2, \dots, n\}$, define
$S(a) = \sum_{i=1}^n c_i a_i$. Prove that there exist two permutations
$a ≠ b$ of $\{1, 2, \dots, n\}$ such that $n!$ is a divisor of $S(a) - S(b)$.
-/

namespace Imo2001Q4

open Equiv Finset
open scoped Nat

variable {n : ℕ} {c : Fin n → ℤ}

/-- The function `S` in the problem. As implemented here it accepts a
permutation of `Fin n` rather than `Icc 1 n`, and as such contains `+ 1`
to compensate. -/
def S (c : Fin n → ℤ) (a : Perm (Fin n)) : ℤ := ∑ i, c i * (a i + 1)


/- ALT (C): splits the conjunction hypothesis `Odd n ∧ 1 < n` into two separate hypotheses. -/
theorem imo2001_p4_alt (hodd : Odd n) (hlt : 1 < n) :
    ∃ a b, a ≠ b ∧ (n ! : ℤ) ∣ S c a - S c b := by sorry

end Imo2001Q4
