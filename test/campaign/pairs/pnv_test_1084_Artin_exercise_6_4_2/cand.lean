import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (hG : Fintype G) (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hcard : Fintype.card G = p * q) : ∃ (N : Subgroup G), N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := sorry
