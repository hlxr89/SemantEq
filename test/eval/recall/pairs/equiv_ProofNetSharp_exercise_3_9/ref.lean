/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Shakarchi.exercise_3_9  (source: Shakarchi)
-/
import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology


/-- Show that $\int_0^1 \log(\sin \pi x) dx = - \log 2$. -/
theorem exercise_3_9 : ∫ x in (0 : ℝ)..(1 : ℝ), Real.log (Real.sin (Real.pi * x)) = - Real.log 2 :=
sorry
