import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} (φ : G →* G) : ∀ (g : G), g ∈ P → φ g ∈ P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ g hg
  obtain ⟨g, hg, rfl⟩ := hg
  exact dummy_assumed φ.toMonoidHom g hg
