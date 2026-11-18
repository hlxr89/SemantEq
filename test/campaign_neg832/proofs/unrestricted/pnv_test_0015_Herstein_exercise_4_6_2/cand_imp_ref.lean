import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (hn : 0 < n) (a b : ℕ) (h : a * b = n) (ha : Irreducible a) (hb : Irreducible b) : Irreducible n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  have h2 : Irreducible (2 : ℕ) := by
    rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
    exact Nat.prime_two
  have h4 : Irreducible (4 : ℕ) := by
    exact dummy_assumed (n := 4) (by norm_num) 2 2 (by norm_num) h2 h2
  have hp4 : Nat.Prime 4 := by
    rw [Nat.prime_iff]
    exact (Nat.irreducible_iff_prime.mp h4)
  norm_num at hp4
