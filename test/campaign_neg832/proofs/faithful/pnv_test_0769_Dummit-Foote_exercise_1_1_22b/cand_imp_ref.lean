import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {a b c : G} : a * b = a * c → b = c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  have cyclic (x y : G) (m : ℕ) : x * (y * x) ^ m = (x * y) ^ m * x := by
    induction m with
    | zero => simp
    | succ m ih => simp only [pow_succ]
                   rw [← mul_assoc, ih]
                   simp only [mul_assoc]
  constructor
  · intro h
    apply dummy_assumed
    calc
      a * (b * a) ^ n = (a * b) ^ n * a := cyclic a b n
      _ = a * 1 := by simp [h]
  · intro h
    apply dummy_assumed
    calc
      b * (a * b) ^ n = (b * a) ^ n * b := cyclic b a n
      _ = b * 1 := by simp [h]
