/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Pugh.exercise_2_57  (source: Pugh)
-/
import Mathlib

open Filter Real Function
open scoped Topology
noncomputable section


/-- Show that if $S$ is connected, it is not true in general that its interior is connected. -/
theorem exercise_2_57 {X : Type*} [TopologicalSpace X]
  : ∃ (S : Set X), IsConnected S ∧ ¬ IsConnected (interior S) :=
sorry
