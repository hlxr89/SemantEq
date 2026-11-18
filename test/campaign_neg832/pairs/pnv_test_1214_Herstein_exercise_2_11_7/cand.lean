import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (hP : IsPGroup p P) (φ : G ≃* G) : φ.toEquiv '' P = P := sorry
