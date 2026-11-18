import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R M : Type*} [Field R] [AddCommGroup M] [Module R M] [Subsingleton R] : ¬ (∃ (U : Finset (Submodule R M)) (hU : U.Nonempty), (⨆ W ∈ U, W) ≤ ⊤) := sorry
