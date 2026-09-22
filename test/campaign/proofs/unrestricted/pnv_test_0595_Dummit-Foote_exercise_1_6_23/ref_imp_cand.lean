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
  intro hs2
  have hσinj : Function.Injective σ := by
    intro a b hab
    simpa only [hs2] using congrArg σ hab
  have hσsurj : Function.Surjective σ := by
    intro a
    exact ⟨σ a, hs2 a⟩
  let τ : MulAut G := MulEquiv.ofBijective σ ⟨hσinj, hσsurj⟩
  exact exercise_1_6_23_assumed τ hs hs2
