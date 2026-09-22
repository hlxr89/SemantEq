import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy (G : Type*) [Group G] [Fintype G] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hcard : Fintype.card G = p * q) : ¬IsSimpleGroup G := sorry
