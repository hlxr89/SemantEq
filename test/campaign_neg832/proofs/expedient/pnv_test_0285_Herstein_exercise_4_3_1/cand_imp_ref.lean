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
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change x * a = 0 at hx
        change y * a = 0 at hy
        simpa [add_mul, hx, hy]
      smul_mem' := by
        intro c x hx
        change x * a = 0 at hx
        simpa [mul_assoc, hx] }
  exact ⟨I, rfl⟩
