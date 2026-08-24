/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Munkres.exercise_13_5a  (source: Munkres)
-/
import Mathlib

open Filter Set TopologicalSpace
open scoped Topology
noncomputable section


def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)


/- ALT (G local-def inlining): the local def `is_topology X T` is inlined into the set-builder predicate -/
theorem exercise_13_5a_alt {X : Type*}
  [TopologicalSpace X] (A : Set (Set X)) (hA : IsTopologicalBasis A) :
  generateFrom A = generateFrom (sInter {T | (univ ∈ T ∧
    (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
    (∀ s, (∀ t ∈ s, t ∈ T) → sUnion s ∈ T)) ∧ A ⊆ T}) :=
sorry
