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
theorem dummy {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K] {a : K} (h : IsAlgebraic F (a^2)) : IsAlgebraic F a := by
  let E : Subfield K := (algebraMap F K).fieldRange
  let e : F ≃+* E := (algebraMap F K).rangeRestrictFieldEquiv
  have he : (algebraMap E K).comp e.toRingHom = algebraMap F K := by
    ext y
    rfl
  have he' : (algebraMap F K).comp e.symm.toRingHom = algebraMap E K := by
    ext y
    simp only [RingHom.comp_apply, Subfield.algebraMap_ofSubfield,
      Subfield.coe_subtype]
    exact (algebraMap F K).rangeRestrictFieldEquiv_apply_symm_apply y
  have bridge (x : K) : IsAlgebraic F x ↔ IsAlgebraic E x := by
    constructor
    · rintro ⟨p, hp, hpx⟩
      refine ⟨p.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hp, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, he]
      exact hpx
    · rintro ⟨p, hp, hpx⟩
      refine ⟨p.map e.symm.toRingHom, (Polynomial.map_ne_zero_iff e.symm.injective).2 hp, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, he']
      exact hpx
  exact bridge a |>.2 (exercise_5_3_7_assumed (bridge (a ^ 2) |>.1 h))
