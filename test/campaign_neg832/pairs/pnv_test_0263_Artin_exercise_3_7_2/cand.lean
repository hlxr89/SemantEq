import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] : ¬ (∃ S : Finset (Submodule F V), (⊤ : Submodule F V) = S.sup id) := sorry
