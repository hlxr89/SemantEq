import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (x : G) {n : ℕ} (hx : x^n = 1) (hn : 0 < n) : x^(n - 1) = x⁻¹ := sorry
