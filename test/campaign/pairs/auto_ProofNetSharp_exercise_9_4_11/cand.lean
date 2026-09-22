/-
Autoformalized from NL only (blind); benchmark: ProofNetSharp; problem: exercise_9_4_11.
-/
import Mathlib

open MvPolynomial

/-- Prove that $x^2+y^2-1$ is irreducible in $\mathbb{Q}[x,y]$. -/
theorem exercise_9_4_11 :
    Irreducible (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) :=
  sorry
