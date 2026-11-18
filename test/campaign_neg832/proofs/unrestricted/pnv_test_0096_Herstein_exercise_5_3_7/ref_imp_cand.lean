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
  exact (IsIntegral.of_pow (n := 2) (by omega) ha.isIntegral).isAlgebraic
