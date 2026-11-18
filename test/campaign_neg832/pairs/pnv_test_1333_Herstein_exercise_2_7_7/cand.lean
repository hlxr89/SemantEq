import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G G' : Type*} [Group G] [Group G'] {ϕ : G →* G'} (hϕ : Function.Surjective ϕ) {N : Subgroup G} (hN : N.Normal) : (N.map ϕ).Normal := sorry
