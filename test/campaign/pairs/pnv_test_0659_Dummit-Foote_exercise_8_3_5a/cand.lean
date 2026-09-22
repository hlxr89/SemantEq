import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℤ) (hn : Squarefree n) (hn_gt_3 : 3 < n) : Irreducible (2 : ℤ√(-n)) ∧ Irreducible (⟨0, 1⟩ : ℤ√(-n)) ∧ Irreducible (⟨1, 1⟩ : ℤ√(-n)) := sorry
