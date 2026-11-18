import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (E : Set ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f E) (h : ¬∃ g : ℝ → ℝ, Continuous g ∧ ∀ x ∈ E, g x = f x) : ∃ ε : ℝ, ε > 0 ∧ ∀ δ : ℝ, δ > 0 → ∃ x ∈ E, ∀ y ∈ E, dist x y < δ → dist (f x) (f y) ≥ ε := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  let E : Set ℝ := Set.Ioi 0
  let f : ℝ → ℝ := fun x => x⁻¹
  have hf : ContinuousOn f E := by
    intro x hx
    dsimp [E] at hx
    dsimp [f]
    exact ((continuousAt_id : ContinuousAt (fun y : ℝ => y) x).inv₀
      (ne_of_gt (show 0 < x from hx))).continuousWithinAt
  have hne : ¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x := by
    rintro ⟨g, hg, heq⟩
    have hbdd : BddAbove (g '' Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.bddAbove_image hg.continuousOn
    rcases hbdd with ⟨M, hM⟩
    let x : ℝ := 1 / (|M| + 1)
    have hden : 0 < |M| + 1 := by positivity
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hxle : x ≤ 1 := by
      dsimp [x]
      exact (div_le_one hden).2 (by linarith [abs_nonneg M])
    have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxpos.le, hxle⟩
    have hbound : g x ≤ M := hM ⟨x, hxmem, rfl⟩
    have hfx : f x = g x := heq x hxpos
    have hinv : f x = |M| + 1 := by
      dsimp [f, x]
      rw [inv_div]
      simp
    rw [hinv] at hfx
    linarith [le_abs_self M]
  exact ⟨E, f, hf, hne⟩
