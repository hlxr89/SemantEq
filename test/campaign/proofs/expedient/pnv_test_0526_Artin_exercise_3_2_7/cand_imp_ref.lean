import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {K L : Type*} [Field K] [Field L] (φ : K →+* L) : Function.Injective φ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ := by
  exact φ.injective
