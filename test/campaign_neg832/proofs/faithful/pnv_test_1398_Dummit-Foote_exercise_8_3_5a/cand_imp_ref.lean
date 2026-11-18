import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℤ} (hn₁ : n > 3) (hn₂ : Nat.Prime (Int.natAbs n)) (hn₃ : ¬(∃ k, k ^ 2 = n)) (a : ℤ√(-n)) (ha₁ : a ≠ 0) (ha₂ : a.norm < n) : Irreducible a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  -- not proved: Squarefree n does not provide the Nat.Prime hypothesis required by dummy_assumed
  sorry
