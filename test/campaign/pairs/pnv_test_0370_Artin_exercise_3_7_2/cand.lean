import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] {S : Finset (Submodule F V)} (hS : ∀ W ∈ S, W ≠ ⊤) : (⋃ W ∈ S, (W : Set V)) ≠ (⊤ : Submodule F V) := sorry
