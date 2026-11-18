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
  have h4 : Irreducible (4 : ℤ√(-101)) := dummy_assumed
    (n := 101)
    (by norm_num)
    (by norm_num)
    (by
      simpa [IsSquare, pow_two, eq_comm] using
        (show Prime (101 : ℤ) by norm_num).not_isSquare)
    (4 : ℤ√(-101))
    (by norm_num)
    (by norm_num [Zsqrtd.norm])
  have hnot4 : ¬ Irreducible (4 : ℤ√(-101)) := by
    intro h
    have hu := h.isUnit_or_isUnit (show (4 : ℤ√(-101)) = 2 * 2 by norm_num)
    rcases hu with hu | hu <;>
      have hnorm := (Zsqrtd.norm_eq_one_iff).2 hu <;>
      norm_num [Zsqrtd.norm] at hnorm
  exact (hnot4 h4).elim
