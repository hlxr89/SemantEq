import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R] [IsPrincipalIdealRing R] [IsDedekindDomain R] (n : ℕ) (hn : Nat.Prime n) (hn1 : n ≠ 1) (hn3 : 3 < n) : Irreducible (n : R) ∧ Irreducible (1 + (n : R)) ∧ Irreducible ((n : R) * (1 - (n : R))) := sorry
