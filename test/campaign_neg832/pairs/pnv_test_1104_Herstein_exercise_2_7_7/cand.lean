import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (N : Subgroup G) [HN : N.Normal] (h : N.map φ = ⊤) : φ.range.Normal := sorry
