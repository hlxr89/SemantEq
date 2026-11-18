import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [CharP F p] (n : ℕ) (hpn : p^n ≠ 0) : ∀ x : F, x ≠ 1 → x^(p^n) ≠ x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  have hpn : p ^ n ≠ 0 := pow_ne_zero n hp
  have hfalse : False :=
    dummy_assumed (F := F) n hpn 0 (by simp) (by simp [zero_pow hpn])
  exact hfalse.elim
