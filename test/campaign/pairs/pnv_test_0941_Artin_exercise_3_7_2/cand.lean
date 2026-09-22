import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] (s : Finset (Submodule F V)) (hs : ∀ W ∈ s, W ≠ ⊤) : (⋃ W ∈ s, (W : Set V)) ≠ (⊤ : Submodule F V) := sorry
