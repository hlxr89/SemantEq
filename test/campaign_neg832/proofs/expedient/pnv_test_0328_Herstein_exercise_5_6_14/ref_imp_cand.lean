import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_6_14_assumed {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F : Type*} [Field F] [CharP F p] (m : ℕ) (hn : m = p ^ n) : ∀ (x : F), x ^ m ≠ x → x ≠ (x ^ p) ^ n := by
  -- not proved: false when p = 2, n = 3, and x is a primitive fifth root in characteristic 2
  sorry
