import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (hn : n > 3 ∧ Nat.Prime n) (a : ℤ√(-n)) (ha : a ≠ 0) : Irreducible a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  -- not proved: squarefree integer n need not be prime, so the antecedent cannot be instantiated for the goal's ring
  sorry
