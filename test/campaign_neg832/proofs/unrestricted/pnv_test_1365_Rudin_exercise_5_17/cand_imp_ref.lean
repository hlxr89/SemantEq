import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1:ℝ) 1)) (hf' : ContinuousOn (deriv f) (Set.Icc (-1:ℝ) 1)) (hf'' : ContinuousOn (deriv (deriv f)) (Set.Icc (-1:ℝ) 1)) (hf''' : ContinuousOn (deriv (deriv (deriv f))) (Set.Icc (-1:ℝ) 1)) (hf'0 : deriv f 0 = 0) (hf'1 : deriv f 1 = 1) : ∃ x ∈ Set.Icc (-1:ℝ) 1, deriv (deriv (deriv f)) x = 3 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_17
  {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f (Set.Icc (-1) 1))
  (hf'' : DifferentiableOn ℝ (deriv f) (Set.Icc (-1) 1))
  (hf''' : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc (-1) 1))
  (hf0 : f (-1) = 0)
  (hf1 : f 0 = 0)
  (hf2 : f 1 = 1)
  (hf3 : deriv f 0 = 0) :
  ∃ x, x ∈ Set.Ioo (-1 : ℝ) 1 ∧ deriv (deriv (deriv f)) x ≥ 3 := by
  have hfalse : False := by
    have hd1 : deriv (fun y : ℝ => y ^ 2 / 2) = fun y : ℝ => y := by
      funext y
      convert (((hasDerivAt_id y).pow 2).div_const 2).deriv using 1 <;> simp [id] <;> ring
    have hd2 : deriv (deriv (fun y : ℝ => y ^ 2 / 2)) = fun _ : ℝ => 1 := by
      rw [hd1]
      funext y
      simp
    have hd3 : deriv (deriv (deriv (fun y : ℝ => y ^ 2 / 2))) = fun _ : ℝ => 0 := by
      rw [hd2]
      funext y
      simp
    obtain ⟨x, hx, hthird⟩ := dummy_assumed
      (f := fun y : ℝ => y ^ 2 / 2)
      (by fun_prop)
      (by rw [hd1]; fun_prop)
      (by rw [hd2]; fun_prop)
      (by rw [hd3]; fun_prop)
      (by rw [hd1])
      (by rw [hd1])
    rw [hd3] at hthird
    norm_num at hthird
  exact hfalse.elim
