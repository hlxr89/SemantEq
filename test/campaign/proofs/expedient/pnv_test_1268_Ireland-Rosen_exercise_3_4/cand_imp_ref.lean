import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed { h : ¬ ∃ (x y : ℤ), 3 * x ^ 2 + 2 = y ^ 2 } : true := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_4 : ¬ ∃ x y : ℤ, 3*x^2 + 2 = y^2 := by
  rintro ⟨x, y, h⟩
  have hm := congrArg (fun z : ℤ => z % 3) h
  have hy : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hy with hy | hy | hy <;>
    norm_num [pow_two, Int.add_emod, Int.mul_emod, hy] at hm
