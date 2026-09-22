import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [MetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hne : (A : Set M).Nonempty ∧ (B : Set M).Nonempty) : ∃ (a₀ : M) (b₀ : M), a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M), a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := sorry
