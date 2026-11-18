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
  have hmono : Monotone f := exercise_4_15_assumed hf hf_open
  left
  exact hmono.strictMono_of_injective (by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · have hconst : ∀ z ∈ Set.Icc x y, f z = f x := by
        intro z hz
        apply le_antisymm
        · calc
            f z ≤ f y := hmono hz.2
            _ = f x := hxy.symm
        · exact hmono hz.1
      have himage : f '' Set.Ioo x y = {f x} := by
        ext w
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa using hconst z ⟨hz.1.le, hz.2.le⟩
        · intro hw
          have hw' : w = f x := by simpa using hw
          refine ⟨(x + y) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          rw [hw']
          exact hconst ((x + y) / 2) ⟨by linarith, by linarith⟩
      have hs : IsOpen ({f x} : Set ℝ) := by
        rw [← himage]
        exact hf_open _ isOpen_Ioo
      obtain ⟨ε, hε, hiso⟩ := Metric.isOpen_singleton_iff.mp hs
      have hnear : dist (f x + ε / 2) (f x) < ε := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
        linarith
      have := hiso (f x + ε / 2) hnear
      linarith
    · exact heq
    · have hconst : ∀ z ∈ Set.Icc y x, f z = f y := by
        intro z hz
        apply le_antisymm
        · calc
            f z ≤ f x := hmono hz.2
            _ = f y := hxy
        · exact hmono hz.1
      have himage : f '' Set.Ioo y x = {f y} := by
        ext w
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa using hconst z ⟨hz.1.le, hz.2.le⟩
        · intro hw
          have hw' : w = f y := by simpa using hw
          refine ⟨(y + x) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          rw [hw']
          exact hconst ((y + x) / 2) ⟨by linarith, by linarith⟩
      have hs : IsOpen ({f y} : Set ℝ) := by
        rw [← himage]
        exact hf_open _ isOpen_Ioo
      obtain ⟨ε, hε, hiso⟩ := Metric.isOpen_singleton_iff.mp hs
      have hnear : dist (f y + ε / 2) (f y) < ε := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
        linarith
      have := hiso (f y + ε / 2) hnear
      linarith)
