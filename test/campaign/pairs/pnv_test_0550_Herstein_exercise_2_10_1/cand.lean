import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b ∉ A) (hb' : orderOf b = p) : A ⊓ Subgroup.closure {b} = ⊥ := sorry
