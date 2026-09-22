/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Singapore2019P4_refs`, proof replaced by `sorry`.
-/
import Mathlib

/-!
# Singapore Math Olympiad (Senior) 2019 (Round 1), Problem 4

http://www.realsutra.com/limjeck/SMO_Senior_2019.pdf

If $\log_{21} 3 = x$, express $\log_7 9$ in terms of $x$.
-/

open Real

noncomputable def solution (x : ℝ) : ℝ := 2*x / (1-x)

theorem Singapore2019P4_refs (x : ℝ) (hx : Real.logb 21 3 = x) :
    Real.logb 7 9 = solution x := by sorry
