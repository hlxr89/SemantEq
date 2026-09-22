import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hc : Fintype.card G = p * q) : ¬ IsSimpleGroup G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  letI : Fact p.Prime := ⟨Nat.prime_iff.mpr hp⟩
  letI : Fact q.Prime := ⟨Nat.prime_iff.mpr hq⟩
  intro h
  simpa using dummy_assumed hG h
