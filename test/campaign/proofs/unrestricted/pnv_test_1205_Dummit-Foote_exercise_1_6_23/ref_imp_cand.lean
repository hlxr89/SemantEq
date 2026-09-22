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
  let τ : MulAut G := MulEquiv.ofBijective σ ⟨
    fun x y hxy ↦ by
      calc
        x = σ (σ x) := (hσ2 x).symm
        _ = σ (σ y) := congrArg σ hxy
        _ = y := hσ2 y,
    fun y ↦ ⟨σ y, hσ2 y⟩
  ⟩
  exact exercise_1_6_23_assumed τ (by simpa [τ]) (by simpa [τ])
