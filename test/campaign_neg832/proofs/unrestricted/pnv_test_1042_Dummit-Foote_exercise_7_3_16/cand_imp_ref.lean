import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) : (φ '' (center R)) ⊆ center S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_3_16 {R S : Type*} [Ring R] [Ring S]
  {φ : R →+* S} (hf : Function.Surjective φ) :
  φ '' (center R) ⊆ center S := by
  rintro _ ⟨r, hr, rfl⟩
  rw [Semigroup.mem_center_iff] at hr ⊢
  intro s
  obtain ⟨x, rfl⟩ := hf s
  rw [← map_mul, ← map_mul]
  exact congrArg φ (hr x)
