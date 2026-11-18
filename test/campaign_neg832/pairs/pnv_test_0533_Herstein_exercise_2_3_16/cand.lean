import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} [hp : Fact (Nat.Prime p)] [Fact (Nat.card G = p)] : IsCyclic G := sorry
