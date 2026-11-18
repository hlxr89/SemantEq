import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h : IsConnected A) : ∃ x : X, x ∈ frontier A ∧ x ∈ A := sorry
