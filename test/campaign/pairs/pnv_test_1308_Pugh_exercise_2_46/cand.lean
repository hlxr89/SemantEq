import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [MetricSpace M] {A B : Set M} (hA : CompactSpace A) (hB : CompactSpace B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) (hA_disj_B : Disjoint A B) : ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := sorry
