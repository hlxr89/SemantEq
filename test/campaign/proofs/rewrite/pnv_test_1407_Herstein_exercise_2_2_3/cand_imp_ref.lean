import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : ∃ i : ℤ, ∀ a b : G, (a * b) ^ i = a ^ i * b ^ i ∧ (a * b) ^ (i+1) = a ^ (i+1) * b ^ (i+1) ∧ (a * b) ^ (i+2) = a ^ (i+2) * b ^ (i+2)) : ∀ a b : G, a * b = b * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) : 
  ∀ a b : G, a*b = b*a := by
  rw [hP] at hP1
  obtain ⟨n, h₀, h₁, h₂⟩ := hP1
  intro a b
  apply dummy_assumed (a := a) (b := b)
  refine ⟨(n : ℤ), ?_⟩
  intro x y
  constructor
  · simpa only [zpow_natCast] using h₀ x y
  constructor
  · have hn₁ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hn₁]
    simpa only [zpow_natCast] using h₁ x y
  · have hn₂ : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by
      rw [Nat.cast_add, Nat.cast_ofNat]
    rw [← hn₂]
    simpa only [zpow_natCast] using h₂ x y
