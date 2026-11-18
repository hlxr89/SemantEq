import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_15_assumed {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (f : ℝ → ℝ) (hf : Continuous f) (hf_open : IsOpenMap f) : StrictMono f ∨ StrictAnti f := by
  have hmon : Monotone f := exercise_4_15_assumed hf hf_open
  refine Or.inl ?_
  intro a b hab
  -- non-rewrite step: openness upgrades the transported monotonicity to strict monotonicity.
  have hopen : IsOpen (f '' Set.Iio b) := hf_open _ isOpen_Iio
  have hmem : f a ∈ f '' Set.Iio b := ⟨a, hab, rfl⟩
  have hnhds : f '' Set.Iio b ∈ 𝓝 (f a) := hopen.mem_nhds hmem
  obtain ⟨u, hau, hu⟩ := exists_Ico_subset_of_mem_nhds hnhds (exists_gt (f a))
  obtain ⟨y, hay, hyu⟩ := exists_between hau
  obtain ⟨x, hxb, hfx⟩ := hu ⟨hay.le, hyu⟩
  rw [← hfx] at hay
  exact hay.trans_le (hmon hxb.le)
