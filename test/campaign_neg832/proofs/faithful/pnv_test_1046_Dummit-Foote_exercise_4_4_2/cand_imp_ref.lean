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
  have h_neq : (p : ℕ) ≠ (q : ℕ) := by
    intro h
    apply hpq
    exact Subtype.ext h
  obtain ⟨g, hg⟩ := dummy_assumed (p : ℕ) (q : ℕ) ⟨p.2⟩ ⟨q.2⟩ h_neq hG
  letI : Subsingleton G := ⟨fun a b => (hg a).trans (hg b).symm⟩
  exact isCyclic_of_subsingleton
