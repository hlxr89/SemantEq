import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] {p n : ℕ} [hf : CharP F p] : ∀ m : ℕ, m = p^n → ∀ x y : F, x^m = x → y^m = y → x = y := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  have h := dummy_assumed (F := ℚ) (p := 0) (n := 0) 1 (by norm_num)
    (0 : ℚ) 1 (by norm_num) (by norm_num)
  norm_num at h
