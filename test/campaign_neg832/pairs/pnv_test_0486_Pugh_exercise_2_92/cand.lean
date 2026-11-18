import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (hK1 : ∀ n, K n ≠ ∅) (hK2 : ∀ n, ∀ m, m ≤ n → K m ⊆ K n) : ∃ x, ∀ n, x ∈ K n := sorry
