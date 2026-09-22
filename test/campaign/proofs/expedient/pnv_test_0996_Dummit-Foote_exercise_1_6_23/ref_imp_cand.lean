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
theorem dummy {G : Type*} [Group G] [Fintype G] (σ : G →* G) (hσ : ∀ g : G, σ (σ g) = g) (hfix : ∀ g : G, σ g = g ↔ g = 1) : ∀ a b : G, a * b = b * a := by
  exact fun a b ↦ (MonoidHom.FixedPointFree.commute_all_of_involutive
    (fun g hg ↦ (hfix g).mp hg) hσ a b).eq
