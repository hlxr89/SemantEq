import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a b c : G) (h : a * b = c) : a⁻¹ * b⁻¹ = c⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have h := dummy_assumed a as.prod (a * as.prod) rfl
      calc
        (a :: as).prod⁻¹ = a⁻¹ * as.prod⁻¹ := h.symm
        _ = a⁻¹ * (as.reverse.map (λ x => x⁻¹)).prod := congrArg (a⁻¹ * ·) ih
        _ = (as.reverse.map (λ x => x⁻¹)).prod * a⁻¹ := by
          simpa using dummy_assumed a
            ((as.reverse.map (λ x => x⁻¹)).prod)⁻¹
            (a * ((as.reverse.map (λ x => x⁻¹)).prod)⁻¹) rfl
        _ = ((a :: as).reverse.map (λ x => x⁻¹)).prod := by simp
