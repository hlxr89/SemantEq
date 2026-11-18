import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] [DecidableEq G] (p q : ℕ) (hp : Fact p.Prime) (hq : Fact q.Prime) (h_neq : p ≠ q) (hG : Fintype.card G = p * q) : ∃ g : G, ∀ x : G, x = g ^ (Fintype.card G / gcd p q) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  classical
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  letI : Fact (q : ℕ).Prime := ⟨q.property⟩
  obtain ⟨g, hg⟩ := dummy_assumed (G := G) (p : ℕ) (q : ℕ)
    (Fact.mk p.property) (Fact.mk q.property)
    (by
      intro h
      apply hpq
      exact Subtype.ext h)
    hG
  have hall : ∀ x y : G, x = y := fun x y => (hg x).trans (hg y).symm
  letI : Unique G :=
    { default := 1
      uniq := fun x => hall x 1 }
  have hcard : Fintype.card G = 1 := Fintype.card_unique
  have hpq_one : (p : ℕ) * (q : ℕ) = 1 := hG.symm.trans hcard
  have hp_two : 2 ≤ (p : ℕ) := p.property.two_le
  have hq_two : 2 ≤ (q : ℕ) := q.property.two_le
  have hfour : 4 ≤ (p : ℕ) * (q : ℕ) := Nat.mul_le_mul hp_two hq_two
  omega
