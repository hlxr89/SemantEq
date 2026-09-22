import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [hp : Fact p.Prime] (hp31 : p = 31) : Irreducible (X^3 - 9 : Polynomial (ZMod p)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩ -- non-rewrite step
  exact dummy_assumed (p := 31) rfl
