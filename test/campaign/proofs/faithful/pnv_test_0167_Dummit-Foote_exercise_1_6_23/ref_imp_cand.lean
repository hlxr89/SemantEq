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
theorem dummy {G : Type*} [Group G] [Fintype G] (σ : G →* G) (hσ : ∀ g : G, σ (σ g) = g) (hσ_fix : ∀ g : G, σ g = g ↔ g = 1) : ∀ a b : G, a * b = b * a := by
  let σ' : MulAut G :=
    { toFun := σ
      invFun := σ
      left_inv := hσ
      right_inv := hσ
      map_mul' := σ.map_mul }
  exact exercise_1_6_23_assumed σ' hσ_fix hσ
