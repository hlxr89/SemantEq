/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Usa1996P1_refs`, proof replaced by `sorry`.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# USA Mathematical Olympiad 1996, Problem 1

Prove that the average of the numbers n⬝sin(n π / 180)
for n ∈ {2,4,6,…,180} is 1/tan(π/180).
-/

theorem Usa1996P1_refs :
    (1 / (90:ℝ)) * ∑ n ∈ Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by sorry
