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
  letI : DecidableEq G := Classical.decEq G
  let hp : Fact (p : ℕ).Prime := ⟨p.property⟩
  let hq : Fact (q : ℕ).Prime := ⟨q.property⟩
  obtain ⟨g, hg⟩ := dummy_assumed (p : ℕ) (q : ℕ) hp hq (fun h ↦ hpq (Subtype.ext h)) hG
  have hsub : Subsingleton G := ⟨fun x y ↦ (hg x).trans (hg y).symm⟩
  have hcard : Fintype.card G = 1 := Fintype.card_eq_one_iff.mpr ⟨1, fun x ↦ hsub.elim x 1⟩
  have hp_two : 2 ≤ (p : ℕ) := p.property.two_le
  have hprod : (p : ℕ) * (q : ℕ) = 1 := hG.symm.trans hcard
  have hp_one : (p : ℕ) = 1 := Nat.eq_one_of_dvd_one ⟨(q : ℕ), hprod.symm⟩
  omega
