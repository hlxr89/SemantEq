import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i + 1) = a ^ (i + 1) * b ^ (i + 1) ∧ (a * b) ^ (i + 2) = a ^ (i + 2) * b ^ (i + 2)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  subst P
  rcases hP1 with ⟨n, hn, hn1, hn2⟩
  apply dummy_assumed
  refine ⟨n, fun a b => ?_⟩
  constructor
  · simpa only [zpow_natCast] using hn a b
  constructor
  · have e : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    simpa only [e, zpow_natCast] using hn1 a b
  · have e : (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) := by omega
    simpa only [e, zpow_natCast] using hn2 a b
