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
  let S : Subfield K := (algebraMap F K).fieldRange
  let f : F →+* S := (algebraMap F K).codRestrict S (fun x ↦ ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · exact RingHom.injective f
    · intro y
      rcases y.property with ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  let e : F ≃+* S := RingEquiv.ofBijective f hf
  have hcomp : (algebraMap F K).comp e.symm.toRingHom = algebraMap S K := by
    ext x
    change ((e (e.symm x) : S) : K) = (x : K)
    exact congrArg (fun y : S ↦ (y : K)) (e.apply_symm_apply x)
  have hS : IsAlgebraic S (a ^ 2) := by
    rcases h with ⟨p, hp, hpa⟩
    refine ⟨p.map e.toRingHom, ?_, ?_⟩
    · intro hz
      apply hp
      apply Polynomial.map_injective e.toRingHom e.injective
      simpa using hz
    · change Polynomial.eval₂ (algebraMap S K) (a ^ 2) (p.map e.toRingHom) = 0
      rw [Polynomial.eval₂_map]
      change Polynomial.eval₂ (algebraMap F K) (a ^ 2) p = 0
      exact hpa
  have haS : IsAlgebraic S a := exercise_5_3_7_assumed hS
  rcases haS with ⟨p, hp, hpa⟩
  refine ⟨p.map e.symm.toRingHom, ?_, ?_⟩
  · intro hz
    apply hp
    apply Polynomial.map_injective e.symm.toRingHom e.symm.injective
    simpa using hz
  · change Polynomial.eval₂ (algebraMap F K) a (p.map e.symm.toRingHom) = 0
    rw [Polynomial.eval₂_map]
    rw [hcomp]
    exact hpa
