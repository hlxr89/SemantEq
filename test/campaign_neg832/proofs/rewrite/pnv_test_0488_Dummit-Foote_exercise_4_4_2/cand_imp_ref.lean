import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p q : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)] (h : Fintype.card G = p * q) (hG : ∀ x y : G, x * y = y * x) : IsCyclic G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  letI : Fact (Nat.Prime (q : ℕ)) := ⟨q.property⟩
  exact dummy_assumed hG (mul_comm)
