import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy : (Infinite (Set.range (fun (n : ℕ) => Ico (n*2) (n*2 + 1)))) := sorry
