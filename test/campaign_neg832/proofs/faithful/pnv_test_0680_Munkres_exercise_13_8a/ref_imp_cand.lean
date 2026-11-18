import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_13_8a_assumed :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : TopologicalSpace.IsTopologicalBasis (Set.range fun p : ℚ × ℚ => Ioo p.1 p.2) := by
  let Bℝ : Set (Set ℝ) := {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b}
  let Bℚ : Set (Set ℚ) := {S : Set ℚ | ∃ a b : ℚ, a < b ∧ S = Ioo a b}
  have hind : Topology.IsInducing ((↑) : ℚ → ℝ) := ⟨rfl⟩
  have hbasis_preimage : IsTopologicalBasis ((fun S : Set ℝ => ((↑) : ℚ → ℝ) ⁻¹' S) '' Bℝ) :=
    exercise_13_8a_assumed.isInducing hind
  have hpreimage :
      ((fun S : Set ℝ => ((↑) : ℚ → ℝ) ⁻¹' S) '' Bℝ) = Bℚ := by
    ext S
    constructor
    · rintro ⟨T, ⟨a, b, hab, rfl⟩, rfl⟩
      exact ⟨a, b, hab, by ext x; simp⟩
    · rintro ⟨a, b, hab, rfl⟩
      refine ⟨Ioo (a : ℝ) (b : ℝ), ⟨a, b, hab, rfl⟩, ?_⟩
      ext x
      simp
  rw [hpreimage] at hbasis_preimage
  have hfamilies :
      Set.range (fun p : ℚ × ℚ => Ioo p.1 p.2) = insert ∅ Bℚ := by
    ext S
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      by_cases hab : a < b
      · exact Or.inr ⟨a, b, hab, rfl⟩
      · exact Or.inl (Set.Ioo_eq_empty hab)
    · rintro (rfl | ⟨a, b, hab, rfl⟩)
      · exact ⟨(0, 0), by simp⟩
      · exact ⟨(a, b), rfl⟩
  rw [hfamilies]
  exact hbasis_preimage.insert_empty
