/-
Benchmark: Compfiles (dwrensha/compfiles, Apache 2.0)
Problem: Imo1972P3
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic

/-!
# International Mathematical Olympiad 1972, Problem 3

Let m and n be non-negative integers. Prove that

     (2m)!(2n)! / (m!n!(m + n)!)

is an integer.
-/

namespace Imo1972P3

open scoped Nat


/- ALT (D): unfolds the divisibility `a ∣ b` into the explicit witness form `∃ k, b = a * k` -/
theorem imo1972_p3_alt (m n : ℕ) :
    ∃ k, (2 * m)! * (2 * n)! = m ! * n ! * (m + n)! * k := sorry

end Imo1972P3
