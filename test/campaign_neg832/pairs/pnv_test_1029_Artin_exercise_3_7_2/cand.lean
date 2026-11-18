import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] : ¬ (∃ (S : Finset (Submodule F V)) (hS : ∀ s ∈ S, s ≠ ⊤), ⊤ = ⨆ s ∈ S, s) := sorry
