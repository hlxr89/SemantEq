import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h : ∀ x : ℝ, ∃ ε > 0, ∀ y, |y - x| < ε → f y ≠ x) : ∃ (E : Set ℝ)(hEmeas : MeasurableSet E) (hEne : Eᶜ.Nonempty)(hE : ∀ y ∈ E, ContinuousWithinAt f (Eᶜ) y), ¬∃ (g : ℝ → ℝ)(hgc : Continuous g), ∀ z ∈ E, g z = f z := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  have hf : ∀ x : ℝ, ∃ ε > 0, ∀ y, |y - x| < ε → y + 1 ≠ x := by
    intro x
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro y hy
    rw [abs_lt] at hy
    linarith
  obtain ⟨E, hEmeas, hEne, hE, hno⟩ :=
    dummy_assumed (f := fun x : ℝ => x + 1) hf
  exfalso
  apply hno
  refine ⟨fun x : ℝ => x + 1, by fun_prop, ?_⟩
  intro z hz
  rfl
