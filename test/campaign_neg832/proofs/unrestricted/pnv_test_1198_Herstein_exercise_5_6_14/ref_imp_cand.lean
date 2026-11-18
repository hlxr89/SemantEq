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
theorem dummy {F : Type*} [Field F] [hF : CharP F p] (m : ℕ) (h : m = p^n) : (X : Fin m → F) -> (∀ i j : Fin m, i ≠ j -> X i ≠ X j) := by
  -- not proved: the candidate is false for a constant function Fin 2 → ZMod 2, while the antecedent is true
  sorry
