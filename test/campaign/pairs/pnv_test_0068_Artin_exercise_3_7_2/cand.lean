import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F V : Type*} [Field F] [Infinite F] [AddCommGroup V] [Module F V] : ¬ ∃ (s : Finset (Submodule F V)) (hs : ∀ (p : Submodule F V), p ∈ s → p ≠ ⊤), (⊤ : Submodule F V) = s.sup id := sorry
