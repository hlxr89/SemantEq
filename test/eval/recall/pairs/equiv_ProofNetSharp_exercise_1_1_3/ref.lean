/-
Benchmark: ProofNet# (Purewhite2019/rethinking_autoformalization)
Problem: Dummit-Foote.exercise_1_1_3  (source: Dummit-Foote)
-/
import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section


/-- Prove that the addition of residue classes $\mathbb{Z}/n\mathbb{Z}$ is associative. -/
theorem exercise_1_1_3 (n : ℤ) :
  ∀ (a b c : ℤ), (a+b)+c ≡ a+(b+c) [ZMOD n] :=
sorry
