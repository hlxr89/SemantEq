import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [MetricSpace M] (A B : Set M) (hA : CompactSpace A) (hB : CompactSpace B) (hAB : A ∩ B = ∅) (hA0 : Nonempty A) (hB0 : Nonempty B) : ∃ a0 ∈ A, ∃ b0 ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a0 b0 ≤ dist a b := sorry
