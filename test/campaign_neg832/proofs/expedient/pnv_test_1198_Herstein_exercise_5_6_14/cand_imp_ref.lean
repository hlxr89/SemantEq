import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [hF : CharP F p] (m : ℕ) (h : m = p^n) : (X : Fin m → F) -> (∀ i j : Fin m, i ≠ j -> X i ≠ X j) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  subst m
  exact galois_poly_separable p (p ^ n) (dvd_pow (dvd_refl p) hn.ne')
