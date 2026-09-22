import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy [TopologicalSpace X] {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (hK1 : ∀ n, K n ≠ ∅) (hK2 : ∀ m n, m ≤ n → K m ⊆ K n) : ∃ x, ∀ n, x ∈ K n := sorry
