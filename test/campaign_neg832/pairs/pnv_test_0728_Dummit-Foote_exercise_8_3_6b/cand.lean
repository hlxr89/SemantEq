import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3) : IsField (ZMod q) := sorry
