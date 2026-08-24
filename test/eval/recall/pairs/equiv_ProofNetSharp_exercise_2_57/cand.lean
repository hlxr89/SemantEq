/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Pugh.exercise_2_57  (source: Pugh)
-/
import Mathlib

open Filter Real Function
open scoped Topology
noncomputable section


/- ALT (F): counterexample existential ∃ S, P S ∧ ¬ Q S restated as negated universal ¬ ∀ S, P S → Q S -/
theorem exercise_2_57_alt {X : Type*} [TopologicalSpace X]
  : ¬ ∀ (S : Set X), IsConnected S → IsConnected (interior S) :=
sorry
