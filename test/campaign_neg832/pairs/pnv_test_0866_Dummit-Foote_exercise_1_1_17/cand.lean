import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {x : G} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := sorry
