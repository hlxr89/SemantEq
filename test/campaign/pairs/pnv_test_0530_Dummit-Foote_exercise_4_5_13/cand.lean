import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] : (56 : ℕ) = Fintype.card G → ∃ (p : Nat) (hp : Nat.Prime p) (P : Sylow p G), P.Normal := sorry
