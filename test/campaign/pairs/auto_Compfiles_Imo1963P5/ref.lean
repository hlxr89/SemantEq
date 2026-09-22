/-
Gold reference statement (verbatim from dwrensha/compfiles (Apache 2.0), extraction machinery stripped);
theorem renamed `Imo1963P5_refs`, proof replaced by `sorry`.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# International Mathematical Olympiad 1963, Problem 5

Prove that cos(π/7) - cos(2π/7) + cos(3π/7) = 1/2.
-/

open scoped Real

theorem Imo1963P5_refs :
    Real.cos (π/7) - Real.cos (2*π/7) + Real.cos (3*π/7) = 1/2 := by sorry
