import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} (h : Fact p.Prime) {P : Sylow p G} (φ : G ≃* G) : φ '' P = P := sorry
