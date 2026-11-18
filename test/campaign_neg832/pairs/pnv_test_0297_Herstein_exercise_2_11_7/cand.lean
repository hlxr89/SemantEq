import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (f : G ≃* G) : ↑f '' P = P := sorry
