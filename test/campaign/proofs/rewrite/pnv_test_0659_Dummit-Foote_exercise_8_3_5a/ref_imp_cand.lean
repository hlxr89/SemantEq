import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_8_3_5a_assumed {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (n : ℤ) (hn : Squarefree n) (hn_gt_3 : 3 < n) : Irreducible (2 : ℤ√(-n)) ∧ Irreducible (⟨0, 1⟩ : ℤ√(-n)) ∧ Irreducible (⟨1, 1⟩ : ℤ√(-n)) := by
  exact exercise_8_3_5a_assumed hn_gt_3 hn
