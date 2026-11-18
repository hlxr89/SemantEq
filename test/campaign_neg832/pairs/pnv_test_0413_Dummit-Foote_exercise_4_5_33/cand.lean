import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (p : ℕ) [Fact (Nat.Prime p)] {H : Subgroup G} (hH : IsPGroup p H) : ∃! (P : Sylow p G), P ≤ H := sorry
