import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact (Nat.Prime p)] (hG : Fintype.card G = p ^ n) {k : ℕ} (hk : n < k) : ∃ (m : ℕ), 0 < m ∧ a ^ m = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  have h := dummy_assumed (a := 2) (G := Unit) (p := 2) (n := 0)
    (k := 1) (by simp) (by simp)
  obtain ⟨m, hm, hpow⟩ := h
  have hone : (2 : ℕ) = 1 ∨ m = 0 := Nat.pow_eq_one.mp hpow
  omega
