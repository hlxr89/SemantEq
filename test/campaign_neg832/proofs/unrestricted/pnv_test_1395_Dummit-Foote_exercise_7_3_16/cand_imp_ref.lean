import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f) : f '' (center R) ⊆ center S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_center_iff] at hx ⊢
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := hf y
    exact (hx.comm z).map φ
  · simp [mul_assoc]
  · simp [mul_assoc]
