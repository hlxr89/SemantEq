import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G G' : Type*} [Group G] [Group G'] {N : Subgroup G} (φ : G →* G') (hN : N.Normal) : (φ.ker.map φ).Normal := sorry
