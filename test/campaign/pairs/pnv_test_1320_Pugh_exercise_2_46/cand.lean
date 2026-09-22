import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {X : Type*} [MetricSpace X] {A B : Set X} (hAB : IsCompact A) (hAB' : IsCompact B) (hAB'' : Disjoint A B) (hA : Set.Nonempty A) (hB : Set.Nonempty B) : ∃ (a₀ : X) (b₀ : X), a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : X), a ∈ A → ∀ (b : X), b ∈ B → dist a₀ b₀ ≤ dist a b := sorry
