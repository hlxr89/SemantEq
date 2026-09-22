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
theorem dummy {G : Type*} [Group G] [Fintype G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) (hG : Fintype.card G = p * q) (hGabelian : ∀ a b : G, a * b = b * a) : IsCyclic G := by
  letI : CommGroup G := { inferInstanceAs (Group G) with
    mul_comm := hGabelian }
  exact exercise_4_4_2_assumed
    (p := ⟨p, hp.out⟩) (q := ⟨q, hq.out⟩)
    (fun h => hpq (congrArg Subtype.val h)) (by simpa using hG)
