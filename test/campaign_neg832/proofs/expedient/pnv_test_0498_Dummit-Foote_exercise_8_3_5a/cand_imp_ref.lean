import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] {n : ℕ} (hn : 3 < n) [Fact (Nat.Prime (Nat.succ n))] (hR : ∀ x : R, x^2 + n ≠ 0) (h2 : Irreducible (2 : R)) (h3 : Irreducible (3 : R)) : Irreducible (2 : R) ∧ Irreducible (1 + 3 : R) ∧ Irreducible (3 : R) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  letI : Fact (Nat.Prime (Nat.succ 4)) := ⟨by norm_num⟩
  have h := dummy_assumed (R := ℤ) (n := 4) (by omega)
    (hR := by intro x; norm_num; nlinarith [sq_nonneg x])
    (h2 := by norm_num [irreducible_iff_prime])
    (h3 := by norm_num [irreducible_iff_prime])
  have h4 : Irreducible (4 : ℤ) := by simpa using h.2.1
  have hu : IsUnit (2 : ℤ) ∨ IsUnit (2 : ℤ) :=
    h4.isUnit_or_isUnit (show (4 : ℤ) = 2 * 2 by norm_num)
  exact (hu.elim h.1.not_isUnit h.1.not_isUnit).elim
