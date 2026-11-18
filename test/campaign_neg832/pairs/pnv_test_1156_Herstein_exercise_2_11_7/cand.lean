import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} {P : Subgroup G} [hp : Fact p.Prime] (hP : P.Normal) (hSylow : IsPGroup p P) (ϕ : G ≃* G) : ϕ.toMonoidHom '' P = P := sorry
