import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {q : ℕ} [Fact (Nat.Prime q)] (hq : q ≡ 3 [MOD 4]) : IsField (Zsqrtd q) := sorry
