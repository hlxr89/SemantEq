/-
Autoformalized from NL only (blind); benchmark: Compfiles; problem: Singapore2019P4.
-/
import Mathlib

/-- The answer: log₇ 9 expressed in terms of x = log₂₁ 3. -/
noncomputable def Singapore2019P4_solution : ℝ → ℝ := fun x => 2 * x / (1 - x)

/-- If $\log_{21} 3 = x$, express $\log_7 9$ in terms of $x$. -/
theorem Singapore2019P4 (x : ℝ) (hx : Real.logb 21 3 = x) :
    Real.logb 7 9 = Singapore2019P4_solution x :=
  sorry
