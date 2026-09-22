import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {X : Type*} [MetricSpace X] {A B : Set X} (hAB : Disjoint A B) (hA : IsCompact A) (hB : IsCompact B) (hAne : Set.Nonempty A) (hBne : Set.Nonempty B) : ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := sorry
