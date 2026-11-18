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
  letI : Zsqrtd.Nonsquare 2 :=
    ⟨fun n h => Nat.prime_two.not_isSquare ⟨n, h⟩⟩
  letI : NoZeroDivisors (Zsqrtd 2) :=
    { eq_zero_or_eq_zero_of_mul_eq_zero := Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero }
  letI : IsDomain (Zsqrtd 2) := NoZeroDivisors.to_isDomain _
  apply dummy_assumed
  simpa only [pow_two] using (Zsqrtd.dmuld (d := 2))
