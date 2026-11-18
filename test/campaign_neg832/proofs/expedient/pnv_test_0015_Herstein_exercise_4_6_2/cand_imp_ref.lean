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
  have h6 : Irreducible (6 : ℕ) :=
    dummy_assumed (n := 6) (by norm_num) 2 3 (by norm_num) Nat.prime_two Nat.prime_three
  have : ¬ Irreducible (6 : ℕ) := by
    rw [Nat.irreducible_iff_prime]
    decide
  exact (this h6).elim
