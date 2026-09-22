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
theorem dummy {G : Type*} [Group G] [Fintype G] (σ : G →* G) (hσ : ∀ g : G, σ g = g ↔ g = 1) (hσ2 : ∀ g : G, σ (σ g) = g) : ∀ a b : G, a * b = b * a := by
  let σ' : MulAut G :=
    { σ with
      invFun := σ
      left_inv := hσ2
      right_inv := hσ2 }
  exact exercise_1_6_23_assumed σ' hσ hσ2
