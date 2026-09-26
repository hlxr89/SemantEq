/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Munkres.exercise_29_10  (source: Munkres)
-/
import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section


/- ALT (B): the four conjuncts of the existential conclusion are permuted (x ∈ V first, IsCompact (closure V) last) -/
theorem exercise_29_10_alt {X : Type*}
  [TopologicalSpace X] [T2Space X] (x : X)
  (hx : ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ (∃ K : Set X, U ⊂ K ∧ IsCompact K))
  (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
  ∃ (V : Set X), x ∈ V ∧ IsOpen V ∧ closure V ⊆ U ∧ IsCompact (closure V) :=
sorry
