import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [Field K] [Fintype K] [CharP K p] (P : Polynomial K) (hP : P.Monic) (hP2 : P.coeff 0 = 1) (hP1 : P.coeff 1 = 1) (hP2P1 : P.coeff 2 = 2) : ¬ ∃ (Q R : Polynomial K), P = Q * R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  let P : Polynomial (ZMod 3) := X ^ 3 + 2 * X ^ 2 + X + 1
  have hP : P.Monic := by
    dsimp [P]
    monicity
    all_goals norm_num
  have hP0 : P.coeff 0 = 1 := by
    norm_num [P, Polynomial.coeff_one]
  have hP1 : P.coeff 1 = 1 := by
    norm_num [P, Polynomial.coeff_one]
  have hP2 : P.coeff 2 = 2 := by
    norm_num [P, Polynomial.coeff_one, Polynomial.coeff_X]
  have hno := dummy_assumed (p := 3) P hP hP0 hP1 hP2
  exfalso
  apply hno
  exact ⟨P, 1, by simp⟩
