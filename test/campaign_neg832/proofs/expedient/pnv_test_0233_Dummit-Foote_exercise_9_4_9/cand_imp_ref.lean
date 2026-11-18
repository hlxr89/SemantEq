import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra ℚ R] [IsScalarTower ℚ R R] : Irreducible ((Polynomial.X ^ 2 - 2 : Polynomial ℚ).map (algebraMap ℚ R)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  exfalso
  let p := (Polynomial.X ^ 2 - 2 : Polynomial ℚ).map
    (algebraMap ℚ (AlgebraicClosure ℚ))
  have hi : Irreducible p := dummy_assumed (R := AlgebraicClosure ℚ)
  have hpdeg : p.degree = 2 := by
    rw [show p = (Polynomial.X ^ 2 - 2 : Polynomial ℚ).map
      (algebraMap ℚ (AlgebraicClosure ℚ)) from rfl]
    rw [degree_map_eq_of_injective
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
    exact degree_X_pow_sub_C (by decide) _
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by simp [hpdeg])
  apply hi.not_isRoot_of_natDegree_ne_one _ hx
  rw [natDegree_eq_of_degree_eq_some hpdeg]
  norm_num
