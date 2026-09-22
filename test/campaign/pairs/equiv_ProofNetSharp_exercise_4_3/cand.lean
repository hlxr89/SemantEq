/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Rudin.exercise_4_3  (source: Rudin)
-/
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section


/- ALT (A): the zero set is written in set-builder form {p | f p = 0} instead of the preimage f⁻¹' {0} (definitionally, not syntactically, equal) -/
theorem exercise_4_3_alt
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = {p : α | f p = 0})
  : IsClosed z :=
sorry
