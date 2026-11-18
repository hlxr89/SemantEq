import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Ring R] [IsDomain R] (f : R[X]) (h : f = X ^ 4 - 4 * X ^ 3 + 6) : ¬ ∃ (p q : R[X]), p * q = f ∧ 0 < degree p ∧ 0 < degree q := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  exfalso
  apply dummy_assumed (R := ZMod 2) (X ^ 4 - 4 * X ^ 3 + 6) rfl
  refine ⟨X, X ^ 3, ?_, ?_, ?_⟩
  · rw [show (4 : (ZMod 2)[X]) = 0 by
          exact (CharP.cast_eq_zero_iff ((ZMod 2)[X]) 2 4).2 (by norm_num),
        show (6 : (ZMod 2)[X]) = 0 by
          exact (CharP.cast_eq_zero_iff ((ZMod 2)[X]) 2 6).2 (by norm_num)]
    ring
  · simp
  · simp
