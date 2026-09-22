import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [MetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) (h_disjoint : Disjoint A B) : ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := sorry
