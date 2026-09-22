import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_2_assumed {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [CommGroup G] [Fintype G] (h : Fintype.card G = p * q) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : p ≠ q) : IsCyclic G := by
  let p' : Nat.Primes := ⟨p, hp⟩
  let q' : Nat.Primes := ⟨q, hq⟩
  apply exercise_4_4_2_assumed (p := p') (q := q')
  · intro hpq'
    exact hqp (congrArg Subtype.val hpq')
  · exact h
