import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type _} [Field F] [CharZero F] : Irreducible (X^3 - 9 : F[X]) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  exfalso
  have hi : Irreducible (X^3 - 9 : Polynomial (AlgebraicClosure ℚ)) :=
    dummy_assumed (F := AlgebraicClosure ℚ)
  have hdeg : (X^3 - 9 : Polynomial (AlgebraicClosure ℚ)).degree = 3 := by
    simpa using
      (degree_X_pow_sub_C (R := AlgebraicClosure ℚ) (n := 3) (by omega) 9)
  obtain ⟨x, hx⟩ :=
    IsAlgClosed.exists_root (X^3 - 9 : Polynomial (AlgebraicClosure ℚ)) (by simp [hdeg])
  have hdeg_one := degree_eq_one_of_irreducible_of_root hi hx
  rw [hdeg] at hdeg_one
  norm_num at hdeg_one
