import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {p : ℕ} [Fact (Nat.Prime p)] (f : Polynomial (ZMod p)) (hf : f.Monic) (hfd : f.degree > 1) (hp : ∀ (x : ℕ), x < p → p ∣ x^p - x) : Irreducible f := sorry
