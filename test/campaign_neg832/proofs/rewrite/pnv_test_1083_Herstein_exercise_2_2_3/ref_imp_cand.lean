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
  have hcomm : ∀ a b : G, Commute a b := by
    intro a b
    apply commutatorElement_eq_one_iff_commute.mp
    have hab := h a b 1 (-1) 0
    simpa only [zpow_one, zpow_neg, zpow_one, mul_inv_cancel,
      commutatorElement_def] using hab.symm
  apply exercise_2_2_3_assumed
    (P := λ i => ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i) (hP := rfl)
  refine ⟨0, ?_, ?_, ?_⟩
  · intro a b
    simp only [pow_zero, mul_one]
  · intro a b
    simp only [zero_add, pow_one]
  · intro a b
    simpa only [zero_add] using (hcomm a b).mul_pow 2
