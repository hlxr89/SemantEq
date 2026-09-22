import Mathlib

open scoped Real
open Real

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Imo1963P5_refs_assumed :
    Real.cos (π/7) - Real.cos (2*π/7) + Real.cos (3*π/7) = 1/2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo1963P5 :
    cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1 / 2 := by
  exact Imo1963P5_refs_assumed
