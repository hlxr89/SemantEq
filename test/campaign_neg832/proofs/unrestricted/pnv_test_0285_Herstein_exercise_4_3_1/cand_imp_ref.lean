import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type u} [CommRing R] (a : R) : IsPrime (Ideal.span { a }) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_3_1 {R : Type*} [CommRing R] (a : R) :
  ∃ I : Ideal R, {x : R | x*a=0} = I := by
  let I : Ideal R :=
    { carrier := {x : R | x * a = 0}
      zero_mem' := zero_mul a
      add_mem' := by
        intro x y hx hy
        change (x + y) * a = 0
        change x * a = 0 at hx
        change y * a = 0 at hy
        rw [add_mul, hx, hy, add_zero]
      smul_mem' := by
        intro c x hx
        change (c * x) * a = 0
        change x * a = 0 at hx
        rw [mul_assoc, hx, mul_zero] }
  exact ⟨I, rfl⟩
