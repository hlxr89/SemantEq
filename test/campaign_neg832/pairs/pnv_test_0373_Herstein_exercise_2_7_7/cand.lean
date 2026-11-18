import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G G' : Type*} [Group G] [Group G'] (N : Subgroup G) (φ : G →* G') (hφ : Function.Surjective φ) (hN : N.Normal) : (φ.range).Normal := sorry
