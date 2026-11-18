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
theorem dummy {F K : Type*} [Field F] [Field K] [Algebra F K] (a : K) (h : IsAlgebraic F (a^2)) : IsAlgebraic F a := by
  let E : Subfield K := (algebraMap F K).fieldRange
  have hE : IsAlgebraic E (a ^ 2) :=
    h.ringHom_of_comp_eq (algebraMap F K).rangeRestrictField (RingHom.id K)
      (algebraMap F K).rangeRestrictField_bijective.injective (by
        ext x
        rfl)
  have haE : IsAlgebraic E a :=
    exercise_5_3_7_assumed (F := E) hE
  exact haE.of_ringHom_of_comp_eq (algebraMap F K).rangeRestrictField (RingHom.id K)
    (algebraMap F K).rangeRestrictField_bijective.surjective Function.injective_id (by
      ext x
      rfl)
