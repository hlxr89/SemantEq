import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_2_3_assumed {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (h : ∀ a b : G, ∀ i j k : ℤ, (a * b) ^ i * (a * b) ^ j = (a ^ i) * (b ^ i) * (a ^ j) * (b ^ j)) : ∀ a b : G, a * b = b * a := by
  apply exercise_2_2_3_assumed
    (P := λ n => ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) (hP := rfl)
  refine ⟨0, ?_, ?_, ?_⟩
  · simp
  · intro a b
    simpa using h a b 1 0 0
  · intro a b
    simpa only [Int.ofNat_eq_coe, zpow_natCast, pow_zero, mul_one] using
      h a b (Int.ofNat 2) (Int.ofNat 0) 0
