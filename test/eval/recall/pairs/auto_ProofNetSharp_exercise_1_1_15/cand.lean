/-
Autoformalized from NL only (blind); benchmark: ProofNetSharp; problem: exercise_1_1_15.
-/
import Mathlib

/-- Prove that $(a_1a_2\dots a_n)^{-1} = a_n^{-1}a_{n-1}^{-1}\dots a_1^{-1}$ for all
$a_1, a_2, \dots, a_n\in G$. -/
theorem exercise_1_1_15 {G : Type*} [Group G] (l : List G) :
    l.prod⁻¹ = (l.reverse.map fun a => a⁻¹).prod :=
  sorry
