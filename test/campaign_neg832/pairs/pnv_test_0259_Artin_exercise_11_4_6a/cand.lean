import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {p : ℕ} [Field K] [Fintype K] [CharP K p] (P : Polynomial K) (hP : P.Monic) (hP2 : P.coeff 0 = 1) (hP1 : P.coeff 1 = 1) (hP2P1 : P.coeff 2 = 2) : ¬ ∃ (Q R : Polynomial K), P = Q * R := sorry
