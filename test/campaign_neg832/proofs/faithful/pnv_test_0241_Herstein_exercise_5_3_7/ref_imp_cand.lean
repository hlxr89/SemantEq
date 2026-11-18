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
theorem dummy {K F : Type*} [Field K] [Field F] [Algebra F K] {a : K} (ha2 : IsAlgebraic (F) (a^2)) : IsAlgebraic (F) a := by
  let E : Subfield K := (algebraMap F K).fieldRange
  let e : F ≃+* E := RingHom.rangeRestrictFieldEquiv (algebraMap F K)
  have ha2E : IsAlgebraic E (a ^ 2) := by
    rcases ha2 with ⟨p, hp, hpa⟩
    refine ⟨p.map e.toRingHom, Polynomial.map_ne_zero hp, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    simpa [E, e, Polynomial.aeval_def] using hpa
  rcases exercise_5_3_7_assumed ha2E with ⟨p, hp, hpa⟩
  refine ⟨p.map e.symm.toRingHom, Polynomial.map_ne_zero hp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have he : (algebraMap F K).comp e.symm.toRingHom = algebraMap E K := by
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  rw [he]
  simpa [Polynomial.aeval_def] using hpa
