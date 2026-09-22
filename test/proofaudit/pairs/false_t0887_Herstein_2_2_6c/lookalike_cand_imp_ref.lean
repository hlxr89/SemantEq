import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (Group, pow, inv); neither side
-- has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem commutator_pow_eq_one_assumed {G : Type*} [Group G] {n : ℕ}
    (h : ∀ (a b : G), (a * b)^n = a^n * b^n) (a b : G) :
    (a * b * a⁻¹ * b⁻¹)^(n*(n-1)) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
    (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
    ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  intro a b
  -- normalise the exponent through the split n = m + 2 provided by hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact commutator_pow_eq_one_assumed h a b
