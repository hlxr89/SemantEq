/-
Gold reference statement (verbatim from ProofNet#, Dummit-Foote.exercise_1_1_15, Mathlib API migrated);
theorem renamed `exercise_1_1_15_refs`, proof replaced by `sorry`.
-/
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

/-- Prove that $(a_1a_2\dots a_n)^{-1} = a_n^{-1}a_{n-1}^{-1}\dots a_1^{-1}$ for all $a_1, a_2, \dots, a_n\in G$. -/
theorem exercise_1_1_15_refs {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod :=
sorry
