import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (hφ : Function.Surjective φ) {N : Subgroup G} (hN : N.Normal) : (N.map φ).Normal := sorry
