import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 351) : ∃ p : ℕ, ∃ P : Sylow p G, P.toSubgroup.Normal := sorry
