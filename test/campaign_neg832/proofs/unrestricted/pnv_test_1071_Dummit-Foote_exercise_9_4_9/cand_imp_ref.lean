import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] {a : R} (ha2 : a ^ 2 = 2) : Irreducible (X^2 - C a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  letI : Zsqrtd.Nonsquare 2 := by
    constructor
    intro n hn
    rcases n with _ | n
    · norm_num at hn
    · have h : n ≤ 1 := by nlinarith
      interval_cases n <;> norm_num at hn
  apply dummy_assumed (R := Zsqrtd (2 : ℕ)) (a := Zsqrtd.sqrtd)
  simpa [pow_two] using (Zsqrtd.dmuld (d := (2 : ℤ)))
