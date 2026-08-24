/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Rudin.exercise_4_3  (source: Rudin)
-/
import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators
noncomputable section


/-- Let $f$ be a continuous real function on a metric space $X$. Let $Z(f)$ (the zero set of $f$ ) be the set of all $p \in X$ at which $f(p)=0$. Prove that $Z(f)$ is closed. -/
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z :=
sorry
