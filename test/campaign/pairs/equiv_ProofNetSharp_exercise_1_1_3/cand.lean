/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Dummit-Foote.exercise_1_1_3  (source: Dummit-Foote)
-/
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section


/- ALT (B commutation/symmetry): swaps the two sides of the congruence (≡ is symmetric) -/
theorem exercise_1_1_3_alt (n : ℤ) :
  ∀ (a b c : ℤ), a+(b+c) ≡ (a+b)+c [ZMOD n] :=
sorry
