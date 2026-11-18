import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type u_1} {κ : Type u_2} [TopologicalSpace X] [T2Space X] (s : κ → Set X) (hs : ∀ (i : κ), Dense (s i)) (hX : SecondCountableTopology X) (hκ : Countable κ) : ∃ (t : Set X), Dense t ∧ t.Countable := sorry
