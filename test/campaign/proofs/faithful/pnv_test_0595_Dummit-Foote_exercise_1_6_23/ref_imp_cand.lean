import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_6_23_assumed {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (G : Type*) [Group G] [Fintype G] (σ : G →* G) (hs : ∀ g : G, σ g = g ↔ g = 1) : (∀ g : G, σ (σ g) = g) → ∀ (a b : G), a * b = b * a := by
  intro hs2 a b
  let σ' : MulAut G :=
    { toFun := σ
      invFun := σ
      left_inv := hs2
      right_inv := hs2
      map_mul' := σ.map_mul }
  exact exercise_1_6_23_assumed σ' hs hs2 a b
