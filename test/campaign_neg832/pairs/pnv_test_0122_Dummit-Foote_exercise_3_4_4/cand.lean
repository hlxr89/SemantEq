import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [Fintype G] [CommGroup G] (hp : IsPGroup p G): ∀ (d : ℕ), d ∣ Fintype.card G → ∃ H : Subgroup G, H.index = d := sorry
