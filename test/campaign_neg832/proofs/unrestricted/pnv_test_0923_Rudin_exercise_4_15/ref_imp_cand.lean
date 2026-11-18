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
  left
  have hmono : Monotone f := exercise_4_15_assumed hf hf_open
  apply hmono.strictMono_of_injective
  have hne_of_lt : ∀ {a b : ℝ}, a < b → f a ≠ f b := by
    intro a b hab heq
    have hopen : IsOpen (f '' Set.Iio b) := hf_open (Set.Iio b) isOpen_Iio
    have hfa : f a ∈ f '' Set.Iio b := ⟨a, hab, rfl⟩
    obtain ⟨u, hau, hu⟩ :=
      exists_Ico_subset_of_mem_nhds (hopen.mem_nhds hfa) ⟨f a + 1, by linarith⟩
    let z : ℝ := (f a + u) / 2
    have hz_bounds : z ∈ Set.Ico (f a) u := by
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨c, hcb, hcz⟩ := hu hz_bounds
    have hle : f c ≤ f b := hmono (le_of_lt hcb)
    rw [hcz, ← heq] at hle
    dsimp [z] at hle
    linarith
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab_lt | hba_lt
  · exact (hne_of_lt hab_lt) hab
  · exact (hne_of_lt hba_lt) hab.symm
