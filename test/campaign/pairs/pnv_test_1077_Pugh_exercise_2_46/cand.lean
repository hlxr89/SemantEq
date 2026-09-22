import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {M : Type*} [MetricSpace M] [Nonempty M] {A B : Set M} (hA : CompactSpace A) (hB : CompactSpace B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) (hA_B : A ∩ B = ∅) : ∃ (a₀ : M) (b₀ : M), a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M), a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := sorry
