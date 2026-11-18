import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : ℝ → E} {b : ℝ} (hf : ∀ (x : ℝ), x > b → HasDerivAt f (f' x) x) (hdf' : Tendsto f' atTop (𝓝 0)) (hb : ∀ (x : ℝ) (H : x > b), ‖f' x‖ ≤ 1) (hnb : b ≤ 0) : Tendsto (fun x => f (x + 1) - f x) atTop (𝓝 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_5
  {f : ℝ → ℝ}
  (hfd : DifferentiableOn ℝ f (Ioi 0))
  (hf : Tendsto (deriv f) atTop (𝓝 0)) :
  Tendsto (λ x => f (x + 1) - f x) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.1 hf) 1 zero_lt_one
  let c : ℝ := max B 1
  have hcB : B ≤ c := le_max_left B 1
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hderiv : ∀ (x : ℝ), x > 0 →
      HasDerivAt (fun y => f (c + y)) (deriv f (c + x)) x := by
    intro x hx
    have hcx : 0 < c + x := add_pos hc0 hx
    have hh := (hfd.differentiableAt (Ioi_mem_nhds hcx)).hasDerivAt.comp x
      ((hasDerivAt_id x).const_add c)
    change HasDerivAt (fun y => f (c + y)) (deriv f (c + x) * 1) x at hh
    simpa only [mul_one] using hh
  have hderiv_tendsto : Tendsto (fun x => deriv f (c + x)) atTop (𝓝 0) :=
    hf.comp (tendsto_atTop_add_const_left atTop c tendsto_id)
  have hbound : ∀ (x : ℝ), x > 0 → ‖deriv f (c + x)‖ ≤ 1 := by
    intro x hx
    exact le_of_lt (by
      simpa only [Real.dist_eq, sub_zero, Real.norm_eq_abs] using
        hB (c + x) (le_trans hcB (le_add_of_nonneg_right (le_of_lt hx))))
  have hshift := dummy_assumed (f := fun x => f (c + x))
    (f' := fun x => deriv f (c + x)) (b := 0) hderiv hderiv_tendsto hbound le_rfl
  have hback := hshift.comp (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
  change Tendsto (fun x => f (c + ((x + -c) + 1)) - f (c + (x + -c)))
    atTop (𝓝 0) at hback
  simpa only [Function.comp_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    add_neg_cancel, add_zero, zero_add] using hback
