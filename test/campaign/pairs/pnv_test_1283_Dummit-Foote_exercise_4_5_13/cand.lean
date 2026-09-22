import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 56) : ∃ (p : ℕ) (hp : Nat.Prime p) (H : Sylow p G), H.Normal := sorry
