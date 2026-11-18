import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] (hV : FiniteDimensional F V) : ¬ ∃ (n : ℕ), ∃ (Ws : Finset (Submodule F V)), ∀ (W : Submodule F V), W ∈ Ws → W ≠ ⊤ ∧ W ≠ ⊥ := sorry
