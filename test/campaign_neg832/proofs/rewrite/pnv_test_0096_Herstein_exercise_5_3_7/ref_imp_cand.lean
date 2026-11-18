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
theorem dummy {K F : Type*} [Field K] [Field F] [Algebra F K] (a : K) (ha : IsAlgebraic F (a^2)) : IsAlgebraic F a := by
  let f : F →+* K := algebraMap F K
  let f' : F →+* f.fieldRange := f.codRestrict f.fieldRange fun x ↦
    RingHom.mem_fieldRange.mpr ⟨x, rfl⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro x y hxy
      exact f.injective (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp y.property
      exact ⟨x, Subtype.ext hx⟩
  let e : F ≃+* f.fieldRange := RingEquiv.ofBijective f' hf'
  have he : (algebraMap f.fieldRange K).comp e.toRingHom = algebraMap F K := by
    ext x
    rfl
  have halg : IsAlgebraic f.fieldRange (a ^ 2) := by
    rw [isAlgebraic_iff_isIntegral, ← RingEquiv.isIntegral_iff e he,
      ← isAlgebraic_iff_isIntegral]
    exact ha
  have h := exercise_5_3_7_assumed halg
  rw [isAlgebraic_iff_isIntegral]
  exact (RingEquiv.isIntegral_iff e he a).mpr
    (isAlgebraic_iff_isIntegral.mp h)
