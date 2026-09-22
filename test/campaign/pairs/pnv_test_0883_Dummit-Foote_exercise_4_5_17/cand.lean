import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 105) : (∃ P : Sylow 5 G, P.1.Normal) ∧ (∃ Q : Sylow 7 G, Q.1.Normal) := sorry
