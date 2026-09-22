import Mathlib

open Filter Real Function Set
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (hdec : ∀ n, K (n+1) ⊆ K n) (hcov : ∀ n, (K n).Nonempty) : (⋂ n, K n).Nonempty := sorry
