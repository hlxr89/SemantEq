/-
Gold reference statement (verbatim from ProofNet#, Dummit-Foote.exercise_9_4_11, Mathlib API migrated);
theorem renamed `exercise_9_4_11_refs`, proof replaced by `sorry`.
-/
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

/-- Prove that $x^2+y^2-1$ is irreducible in $\mathbb{Q}[x,y]$. -/
theorem exercise_9_4_11_refs :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) :=
sorry
