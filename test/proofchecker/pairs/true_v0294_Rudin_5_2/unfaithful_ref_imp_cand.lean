import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (deriv, DifferentiableOn,
-- StrictMonoOn, pointwise Inv on functions); the unified context is empty.
-- The candidate's auto-bound `a b` are written as explicit implicits, and its
-- unused normed-space parameter E is kept verbatim.

-- ===== assumed statement (antecedent): the reference =====
theorem exercise_5_2_ref_assumed {a b : ℝ}
  {f g : ℝ → ℝ} (hf : ∀ x ∈ Set.Ioo a b, deriv f x > 0)
  (hg : g = f⁻¹) :
  StrictMonoOn f (Set.Ioo a b) ∧
  DifferentiableOn ℝ g (Set.Ioo a b) ∧
  ∀ x ∈ Set.Ioo a b, deriv g (f x) = 1 / deriv f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent: the candidate =====
theorem rudin_5_2_cand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hder : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) :
    StrictMonoOn f (Set.Ioo a b) ∧
    DifferentiableOn ℝ (Inv.inv f) (f '' Set.Ioo a b) ∧
    ∀ x ∈ Set.Ioo a b, deriv (Inv.inv f) (f x) = (deriv f x)⁻¹ := by
  have main := exercise_5_2_ref_assumed (f := f) (g := f⁻¹) hder rfl
  refine ⟨main.1, ?_, fun x hx => by rw [main.2.2 x hx, one_div]⟩
  -- differentiability of the reciprocal on the image interval, via the
  -- reference specialized to the identity map
  have key := (exercise_5_2_ref_assumed (a := (-1 : ℝ)) (b := 1)
      (f := id) (g := id⁻¹) (fun x _ => by norm_num [deriv_id]) rfl).2.2
      0 (by norm_num)
  rw [show ((id : ℝ → ℝ)⁻¹) = fun x : ℝ => x⁻¹ from rfl] at key
  norm_num [deriv_inv, deriv_id] at key
