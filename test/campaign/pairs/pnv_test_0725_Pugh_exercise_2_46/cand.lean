import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [MetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty) : ∃ (a₀ : M) (H : a₀ ∈ A) (b₀ : M) (H : b₀ ∈ B), ∀ (a : M) (H : a ∈ A) (b : M) (H : b ∈ B), dist a₀ b₀ ≤ dist a b := sorry
