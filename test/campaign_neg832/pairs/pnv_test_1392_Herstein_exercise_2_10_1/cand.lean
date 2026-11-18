import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b ^ p = 1) (hp : Nat.Prime p) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := sorry
