import Mathlib

open Filter Real Function
open scoped Topology

theorem dummy {X : Type*} [PseudoMetricSpace X] {A B : Set X} (ha : IsCompact A) (hb : IsCompact B) (hne : (A : Set X).Nonempty) (hne' : (B : Set X).Nonempty) (h : Disjoint A B) : ∃ (a₀ : X)(H : a₀ ∈ A) (b₀ : X)(H : b₀ ∈ B), ∀ (a : X)(ha : a ∈ A) (b : X)(hb : b ∈ B), dist a₀ b₀ ≤ dist a b := sorry
