import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_2_6_assumed {R : Type*} [Ring R] (a x : R)
  (h : a ^ 2 = 0) : a * (a * x + x * a) = (a * x + x * a) * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [CommSemiring R] {a x : R} (h : a^2 = 0) : Commute a (x + x * a) := by
  have htransport := exercise_4_2_6_assumed (R := ZMod 1) 0 0 (by norm_num)
  have hz : (0 : R) = 0 :=
    congrArg (fun _ : ZMod 1 => (0 : R)) htransport
  show a * (x + x * a) = (x + x * a) * a
  calc
    a * (x + x * a) = a * (x + x * a) + 0 := by rw [add_zero]
    _ = a * (x + x * a) + 0 := congrArg (fun z => a * (x + x * a) + z) hz
    _ = (x + x * a) * a := by rw [add_zero, mul_comm]
