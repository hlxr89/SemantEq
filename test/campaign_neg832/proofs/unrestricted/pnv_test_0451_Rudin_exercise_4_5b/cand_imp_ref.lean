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
  let E : Set ℝ := {x | x ≠ 0}
  let f : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  refine ⟨E, f, ?_, ?_⟩
  · intro x hx
    change x ≠ 0 at hx
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · apply ContinuousAt.continuousWithinAt
      apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hxneg] with y hy
      simp [f, hy]
    · apply ContinuousAt.continuousWithinAt
      apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hxpos] with y hy
      simp [f, not_lt.mpr (le_of_lt hy)]
  · rintro ⟨g, hg, hagree⟩
    rcases (Metric.continuousAt_iff.mp hg.continuousAt (1 / 4 : ℝ) (by norm_num)) with
      ⟨δ, hδ, hclose⟩
    have hp : 0 < δ / 2 := by linarith
    have hn : -δ / 2 < 0 := by linarith
    have hpE : δ / 2 ∈ E := by
      change δ / 2 ≠ 0
      exact ne_of_gt hp
    have hnE : -δ / 2 ∈ E := by
      change -δ / 2 ≠ 0
      exact ne_of_lt hn
    have hgp : g (δ / 2) = 1 := by
      rw [← hagree (δ / 2) hpE]
      simp [f, not_lt.mpr (le_of_lt hp)]
    have hgn : g (-δ / 2) = 0 := by
      rw [← hagree (-δ / 2) hnE]
      simp [f, hn]
    have hpdist : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hp]
      linarith
    have hndist : dist (-δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_neg hn]
      linarith
    have hpclose := hclose hpdist
    have hnclose := hclose hndist
    rw [hgp] at hpclose
    rw [hgn, dist_comm] at hnclose
    have htri : dist (1 : ℝ) 0 ≤ dist 1 (g 0) + dist (g 0) 0 :=
      dist_triangle 1 (g 0) 0
    have hbad : dist (1 : ℝ) 0 < 1 / 2 :=
      lt_of_le_of_lt htri (by linarith)
    norm_num [Real.dist_eq] at hbad
