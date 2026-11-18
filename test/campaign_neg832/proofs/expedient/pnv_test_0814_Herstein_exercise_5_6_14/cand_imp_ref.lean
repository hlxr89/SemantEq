import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [CharP F p] (m : ℕ) (hpm : m = p ^ n) : ∀ (x : F), x ≠ 1 → x ^ m ≠ x → x ≠ 0 → x ^ m - x ≠ 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  apply galois_poly_separable p m
  rw [hm]
  exact dvd_pow (dvd_refl p) hn.ne'
