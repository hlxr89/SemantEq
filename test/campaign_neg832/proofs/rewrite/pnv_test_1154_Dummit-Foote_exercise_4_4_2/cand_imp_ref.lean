import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p q : ℕ} (hp : Fact p.Prime) (hq : Fact q.Prime) (hpq : p ≠ q) (hG : Fintype.card G = p * q) : IsCyclic G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  let hp : Fact (p : ℕ).Prime := ⟨p.property⟩
  let hq : Fact (q : ℕ).Prime := ⟨q.property⟩
  apply dummy_assumed hp hq
  · intro hpq_coe
    apply hpq
    exact Subtype.ext hpq_coe
  · exact hG
