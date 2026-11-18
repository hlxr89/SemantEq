import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F V : Type*} [Field F] [Infinite F] [AddCommGroup V] [Module F V] : ¬(∃ (n : ℕ) (f : Fin n → Submodule F V), (⋃ i : Fin n, (f i : Set V)) = Set.univ) := sorry
