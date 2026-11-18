import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_11_7_assumed {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} (φ : G →* G) : ∀ (g : G), g ∈ P → φ g ∈ P := by
  -- not proved: the goal omits both primality of p and normality of P, so the antecedent cannot be instantiated
  sorry
