import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (n : ℕ) [h0 : NeZero n] (a : G) (b : G) (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) : Commute a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  letI : NeZero n := ⟨by omega⟩
  intro a b
  have hab : Commute a b := dummy_assumed n a b h
  have hcomm : a * b * a⁻¹ * b⁻¹ = 1 := by
    rw [hab.eq]
    simp
  rw [hcomm]
  simp
