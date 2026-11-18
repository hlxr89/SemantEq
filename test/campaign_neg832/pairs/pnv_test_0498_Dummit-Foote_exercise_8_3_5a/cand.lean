import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] {n : ℕ} (hn : 3 < n) [Fact (Nat.Prime (Nat.succ n))] (hR : ∀ x : R, x^2 + n ≠ 0) (h2 : Irreducible (2 : R)) (h3 : Irreducible (3 : R)) : Irreducible (2 : R) ∧ Irreducible (1 + 3 : R) ∧ Irreducible (3 : R) := sorry
