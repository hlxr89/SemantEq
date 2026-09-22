import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [PseudoMetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hA0 : A.Nonempty) (hB0 : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, dist a b ≤ dist a' b' := sorry
