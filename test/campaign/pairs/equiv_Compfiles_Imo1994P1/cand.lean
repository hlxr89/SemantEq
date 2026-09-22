/-
Benchmark: Compfiles (dwrensha/compfiles, Apache 2.0)
Problem: Imo1994P1
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

/-!
# International Mathmatical Olympiad 1994, Problem 1

Let `m` and `n` be two positive integers.
Let `a₁, a₂, ..., aₘ` be `m` different numbers from the set `{1, 2, ..., n}`
such that for any two indices `i` and `j` with `1 ≤ i ≤ j ≤ m` and `aᵢ + aⱼ ≤ n`,
there exists an index `k` such that `aᵢ + aⱼ = aₖ`.
Show that `(a₁+a₂+...+aₘ)/m ≥ (n+1)/2`
-/

open Finset

namespace Imo1994P1


/- ALT (A): states the conclusion with `≥` instead of `≤` and the lower bound as `1 ≤ a` instead of `0 < a`. -/
theorem imo1994_p1_alt (n : ℕ) (m : ℕ) (A : Finset ℕ) (hm : A.card = m + 1)
    (hrange : ∀ a ∈ A, 1 ≤ a ∧ a ≤ n)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ≤ n → a + b ∈ A) :
    2 * ∑ x ∈ A, x ≥ (m + 1) * (n + 1) := by sorry

end Imo1994P1
