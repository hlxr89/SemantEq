/-
Gold reference statement (verbatim from ProofNet#, Dummit-Foote.exercise_3_4_5a, Mathlib API migrated);
theorem renamed `exercise_3_4_5a_refs`, proof replaced by `sorry`.
-/
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

/-- Prove that subgroups of a solvable group are solvable. -/
theorem exercise_3_4_5a_refs {G : Type*} [Group G]
  (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
sorry
