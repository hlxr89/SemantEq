import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : IsTopologicalBasis {S : Set ℝ | ∃ (a b : ℚ), S = Ioo ↑a ↑b} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_8a :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := by
  rw [show {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} =
      ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) b} by
    ext S
    simp]
  exact Real.isTopologicalBasis_Ioo_rat
