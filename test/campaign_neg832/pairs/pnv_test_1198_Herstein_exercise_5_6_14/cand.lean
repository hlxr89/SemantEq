import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [hF : CharP F p] (m : ℕ) (h : m = p^n) : (X : Fin m → F) -> (∀ i j : Fin m, i ≠ j -> X i ≠ X j) := sorry
