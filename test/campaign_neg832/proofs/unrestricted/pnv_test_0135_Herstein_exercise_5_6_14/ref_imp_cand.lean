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
theorem dummy {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : (∃ (x : F), x ^ (p ^ n) = x) → (∀ x y : F, x ≠ y → x ^ (p ^ n) ≠ y ^ (p ^ n)) := by
  intro _ x y hxy hpow
  exact hxy (iterateFrobenius_inj F p n hpow)
