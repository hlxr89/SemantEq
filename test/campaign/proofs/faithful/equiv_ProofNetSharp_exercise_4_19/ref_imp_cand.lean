import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_19_assumed
  {f : ℝ → ℝ} (hf : ∀ a b c, a < b → f a < c → c < f b → ∃ x, a < x ∧ x < b ∧ f x = c)
  (hg : ∀ r : ℚ, IsClosed {x | f x = r}) : Continuous f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_19_alt
  {f : ℝ → ℝ} (hf : ∀ a b c, a < b → f a < c → c < f b → ∃ x ∈ Set.Ioo a b, f x = c)
  (hg : ∀ r : ℚ, IsClosed {x | f x = r}) : Continuous f := by
  apply exercise_4_19_assumed ?_ hg
  intro a b c hab hac hcb
  obtain ⟨x, hx, hfx⟩ := hf a b c hab hac hcb
  exact ⟨x, hx.1, hx.2, hfx⟩
