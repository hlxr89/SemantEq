import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [CommGroup G] [Fintype G] (h : Fintype.card G = p * q) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : p ≠ q) : IsCyclic G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  exact dummy_assumed hG p.property q.property (fun h => hpq (Subtype.ext h))
