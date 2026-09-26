/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Imo1983P1_refs`, proof replaced by `sorry`.
-/
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

/-!
# International Mathematical Olympiad 1983, Problem 1

Let ℝ+ be the set of positive real numbers.

Determine all functions f : ℝ+ → ℝ+ which satisfy:
 i) f(xf(y)) = yf(x) for all x y ∈ ℝ+.
 ii) f(x) → 0 as x → ∞.
-/

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

def SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

theorem Imo1983P1_refs (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by sorry
