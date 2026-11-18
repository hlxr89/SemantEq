import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_17_assumed
  {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f (Set.Icc (-1) 1))
  (hf'' : DifferentiableOn ℝ (deriv f) (Set.Icc (-1) 1))
  (hf''' : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc (-1) 1))
  (hf0 : f (-1) = 0)
  (hf1 : f 0 = 0)
  (hf2 : f 1 = 1)
  (hf3 : deriv f 0 = 0) :
  ∃ x, x ∈ Set.Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (h₁ : ContDiff ℝ 3 f) (h₂ : f (-1) = 0) (h₃ : f 0 = 0) (h₄ : f 1 = 1) (h₅ : deriv f 0 = 0) : ∃ x ∈ Set.Icc (-1 : ℝ) 1, deriv^[3] f x ≥ 3 := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl] at h₁
  have hf' : DifferentiableOn ℝ f (Set.Icc (-1) 1) :=
    (contDiff_succ_iff_deriv.mp h₁).1.differentiableOn
  have hderiv : ContDiff ℝ 2 (deriv f) := by
    exact (contDiff_succ_iff_deriv.mp h₁).2.2
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at hderiv
  have hf'' : DifferentiableOn ℝ (deriv f) (Set.Icc (-1) 1) :=
    (contDiff_succ_iff_deriv.mp hderiv).1.differentiableOn
  have hderiv2 : ContDiff ℝ 1 (deriv (deriv f)) := by
    exact (contDiff_succ_iff_deriv.mp hderiv).2.2
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl] at hderiv2
  have hf''' : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc (-1) 1) :=
    (contDiff_succ_iff_deriv.mp hderiv2).1.differentiableOn
  obtain ⟨x, hx, hthird⟩ := exercise_5_17_assumed hf' hf'' hf''' h₂ h₃ h₄ h₅
  refine ⟨x, ⟨hx.1.le, hx.2.le⟩, ?_⟩
  exact hthird
