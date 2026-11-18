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
theorem dummy {R : Type*} [Ring R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥) : ∃ (x : R), x ≠ 0 ∧ x ∈ I := by
  by_contra h
  apply hI
  ext x
  simp only [Ideal.mem_bot]
  constructor
  · intro hx
    by_contra hx0
    exact h ⟨x, hx0, hx⟩
  · rintro rfl
    exact I.zero_mem
