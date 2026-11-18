import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) {f : X → Y} {A : Set X} (hA : IsCompact A) (hf : UniformContinuousOn f A) : ∃ g : X → Y, Continuous g ∧ UniformContinuous g ∧ EqOn f g A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  let F : ℝ → ℕ := fun x ↦ if x = 0 then 0 else 1
  let S : Set ℝ := {0, 1}
  have hS : IsCompact S := Set.toFinite S |>.isCompact
  have hF : UniformContinuousOn F S :=
    hS.uniformContinuousOn_of_continuous (Set.toFinite S |>.continuousOn F)
  obtain ⟨g, hg, _, hFg⟩ := dummy_assumed (inferInstance : CompleteSpace ℕ) hS hF
  have hc : g (0 : ℝ) = g 1 :=
    isPreconnected_univ.constant hg.continuousOn (by simp) (by simp)
  have h0 : g (0 : ℝ) = 0 := by
    simpa [F] using (hFg (by simp [S]) : F 0 = g 0).symm
  have h1 : g (1 : ℝ) = 1 := by
    simpa [F] using (hFg (by simp [S]) : F 1 = g 1).symm
  exact (zero_ne_one (h0.symm.trans (hc.trans h1))).elim
