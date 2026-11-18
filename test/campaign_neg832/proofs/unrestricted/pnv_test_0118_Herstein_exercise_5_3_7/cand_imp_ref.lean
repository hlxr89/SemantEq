import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {K L : Type*} [Field K] [Field L] [Algebra K L] {a : L} (h : IsAlgebraic K (a^2)) : IsAlgebraic K a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := by
  exact dummy_assumed ha
