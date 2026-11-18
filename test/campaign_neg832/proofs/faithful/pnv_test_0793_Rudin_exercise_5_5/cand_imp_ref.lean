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
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hf 1 zero_lt_one
  let c : ℝ := max B 0 + 1
  have hc : 0 < c := by
    dsimp [c]
    linarith [le_max_right B 0]
  have hBc : B ≤ c := by
    dsimp [c]
    linarith [le_max_left B 0]
  have hshift : Tendsto (fun x : ℝ => x + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have hderiv : ∀ x : ℝ, x > 0 →
      HasDerivAt (fun t => f (t + c)) (deriv f (x + c)) x := by
    intro x hx
    have hxc : x + c ∈ Set.Ioi (0 : ℝ) := by
      exact (show 0 < x + c by linarith)
    simpa only [Function.comp_apply, id_eq, mul_one] using
      (hfd.differentiableAt (isOpen_Ioi.mem_nhds hxc)).hasDerivAt.comp x
        ((hasDerivAt_id x).add_const c)
  have hbound : ∀ x : ℝ, x > 0 → ‖deriv f (x + c)‖ ≤ 1 := by
    intro x hx
    exact le_of_lt (by simpa [dist_eq_norm] using hB (x + c) (by linarith))
  have hg := dummy_assumed (f := fun t => f (t + c))
    (f' := fun x => deriv f (x + c)) (b := 0) hderiv (hf.comp hshift) hbound le_rfl
  have hback : Tendsto (fun x : ℝ => x - c) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
  convert hg.comp hback using 1 <;> funext x <;> congr 2 <;> ring
