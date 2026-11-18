import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {I : Ideal (GaussianInt)} (hI : I ≠ ⊥) : ∃ n ≠ (0 : ℤ), (n : GaussianInt) ∈ I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  obtain ⟨n, hn, hnI⟩ := dummy_assumed hI
  refine ⟨⟨(n : GaussianInt), hnI⟩, ?_, ?_⟩
  · intro hz
    apply hn
    have hcast : (n : GaussianInt) = 0 := congrArg Subtype.val hz
    exact_mod_cast hcast
  · simp
