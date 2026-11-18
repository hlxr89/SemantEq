import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_10_6_7_assumed {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {I : Ideal ℤ} (hI : I ≠ ⊥) : ∃ (n : ℤ), n ≠ 0 ∧ n ∈ I := by
  obtain ⟨n, hnI, hn0⟩ := I.ne_bot_iff.mp hI
  exact ⟨n, hn0, hnI⟩
