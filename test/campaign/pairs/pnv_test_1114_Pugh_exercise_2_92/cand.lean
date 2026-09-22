import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {α : Type*} [TopologicalSpace α] [CompactSpace α] {K : ℕ → Set α} (hK : ∀ n, IsCompact (K n)) (hK_nonempty : ∀ n, (K n).Nonempty) (hK_decreasing : ∀ n, K (n + 1) ⊆ K n) : (⋂ n, K n).Nonempty := sorry
