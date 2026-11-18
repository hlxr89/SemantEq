import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] [DecidableEq G] (hp : Fintype.card G = p * q) (hp1 : Fact p.Prime) (hp2 : Fact q.Prime) (h_distinct : p ≠ q) : IsCyclic G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  classical
  apply dummy_assumed hG ⟨p.property⟩ ⟨q.property⟩
  intro hpq_val
  apply hpq
  exact Subtype.ext hpq_val
