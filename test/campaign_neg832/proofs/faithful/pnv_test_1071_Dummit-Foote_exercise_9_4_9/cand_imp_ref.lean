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
  letI : Zsqrtd.Nonsquare 2 := ⟨by
    intro n hn
    have hle : n ≤ 2 := by nlinarith
    interval_cases n <;> norm_num at hn⟩
  letI : NoZeroDivisors (Zsqrtd 2) :=
    ⟨fun h => Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero (d := 2) h⟩
  letI : IsDomain (Zsqrtd 2) := NoZeroDivisors.to_isDomain _
  apply dummy_assumed
  simpa [pow_two] using (Zsqrtd.dmuld (d := 2))
