import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (φ : G →* G) {N : Subgroup G} [hN : N.Normal] : (Subgroup.map φ N).Normal := sorry
