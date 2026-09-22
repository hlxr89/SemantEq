import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_3_7_assumed {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F K : Type*} [Field F] [Field K] [Algebra F K] {a : K} (ha2 : IsAlgebraic F (a^2)) : IsAlgebraic F a := by
  let S : Subfield K := (algebraMap F K).fieldRange
  have hbridge (x : K) : IsAlgebraic S x ↔ IsAlgebraic F x :=
    isAlgebraic_ringHom_iff_of_comp_eq
      (RingHom.rangeRestrictFieldEquiv (algebraMap F K)) (RingEquiv.refl K)
      (RingEquiv.refl K).injective (by ext y; rfl)
  exact (hbridge a).mp (exercise_5_3_7_assumed ((hbridge (a ^ 2)).mpr ha2))
