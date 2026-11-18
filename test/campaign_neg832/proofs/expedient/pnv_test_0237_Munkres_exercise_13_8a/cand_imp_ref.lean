import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [TopologicalSpace α] : TopologicalSpace.IsTopologicalBasis {s : Set ℝ | ∃ (a b : ℚ), (a : ℝ) < b ∧ s = Set.Ioo (a : ℝ) (b : ℝ)} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_8a :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := by
  rw [show {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} =
      {s : Set ℝ | ∃ (a b : ℚ), (a : ℝ) < b ∧ s = Set.Ioo (a : ℝ) (b : ℝ)} by
    ext s
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨a, b, by exact_mod_cast hab, rfl⟩
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨a, b, by exact_mod_cast hab, rfl⟩]
  exact dummy_assumed (α := ℝ)
