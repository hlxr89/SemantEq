import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_7_4_27_assumed {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (R : Type*) [CommRing R] (a : R) (ha : IsNilpotent a) (b : R) : IsUnit (1 - a * b) := by
  rcases ha with ⟨n, hn⟩
  have hprod : IsNilpotent (a, (0 : ℤ)) := by -- non-rewrite step
    refine ⟨n + 1, ?_⟩
    apply Prod.ext
    · change a ^ (n + 1) = 0
      rw [pow_succ, hn, zero_mul]
    · change (0 : ℤ) ^ (n + 1) = 0
      exact zero_pow (Nat.succ_ne_zero n)
  have hnontrivial : (0 : R × ℤ) ≠ 1 := by
    intro h
    exact Int.zero_ne_one (congrArg Prod.snd h)
  have hu := exercise_7_4_27_assumed hnontrivial hprod (b, (0 : ℤ))
  exact hu.map (MonoidHom.fst R ℤ)
