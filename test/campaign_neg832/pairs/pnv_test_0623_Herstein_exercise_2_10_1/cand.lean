import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal] {p : ℕ} [hp : Fact p.Prime] {b : G} (hb : b ^ p = 1) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := sorry
