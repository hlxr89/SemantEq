import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] : Fintype.card G = 56 → ∃ (p : ℕ)(H : Sylow p G), H.Normal := sorry
