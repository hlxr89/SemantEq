/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Munkres.exercise_29_10  (source: Munkres)
-/
import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section


/-- Show that if $X$ is a Hausdorff space that is locally compact at the point $x$, then for each neighborhood $U$ of $x$, there is a neighborhood $V$ of $x$ such that $\bar{V}$ is compact and $\bar{V} \subset U$. -/
theorem exercise_29_10 {X : Type*}
  [TopologicalSpace X] [T2Space X] (x : X)
  (hx : ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ (∃ K : Set X, U ⊂ K ∧ IsCompact K))
  (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
  ∃ (V : Set X), IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ U :=
sorry
