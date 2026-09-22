import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {a b : G} {n : ℕ} (hn : n > 1) (h : ∀ x y : G, (x * y) ^ n = x ^ n * y ^ n) (h' : (a * b) ^ n = a ^ n * b ^ n) (h'' : (a * b * a⁻¹ * b⁻¹) ^ n = a ^ n * b ^ n * a⁻¹ ^ n * b⁻¹ ^ n) : (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  intro a b
  apply dummy_assumed hn h (h a b)
  calc
    (a * b * a⁻¹ * b⁻¹) ^ n = (a * b * a⁻¹) ^ n * (b⁻¹) ^ n := h (a * b * a⁻¹) b⁻¹
    _ = ((a * b) ^ n * (a⁻¹) ^ n) * (b⁻¹) ^ n := by rw [h (a * b) a⁻¹]
    _ = a ^ n * b ^ n * a⁻¹ ^ n * b⁻¹ ^ n := by rw [h a b]
