import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1999_b4_assumed (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (hf : ∀ x, 0 < f x) (hf' : ∀ x, 0 < deriv f x) (hf'' : ∀ x, 0 < deriv^[2] f x) (hf''' : ∀ x, 0 < deriv^[3] f x) (h_bound : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  have hd0 : Differentiable ℝ f := fun x ↦ differentiableAt_of_deriv_ne_zero (ne_of_gt (hf' x))
  have hd1 : Differentiable ℝ (deriv f) := fun x ↦
    differentiableAt_of_deriv_ne_zero (ne_of_gt (by simpa using hf'' x))
  have hd2 : Differentiable ℝ (deriv^[2] f) := fun x ↦
    differentiableAt_of_deriv_ne_zero (ne_of_gt (by simpa [Function.iterate_succ_apply] using hf''' x))
  have hc1d : ContDiff ℝ 1 (deriv f) := contDiff_one_iff_deriv.mpr ⟨hd1, hd2.continuous⟩
  have hc2 : ContDiff ℝ 2 f := by
    exact (contDiff_succ_iff_deriv (n := 1)).mpr ⟨hd0, by simp, hc1d⟩
  intro x
  let F : ℝ → ℝ := fun y ↦ f (-y)
  have hF : ContDiff ℝ 2 F := hc2.comp contDiff_neg
  have hF1 (y : ℝ) : deriv F y = -deriv f (-y) := by
    simpa [F] using ((hd0 (-y)).hasDerivAt.comp y (hasDerivAt_neg y)).deriv
  have hF2 (y : ℝ) : deriv (deriv F) y = (deriv^[2] f) (-y) := by
    rw [show deriv F = fun t ↦ -deriv f (-t) from funext hF1]
    simpa using (((hd1 (-y)).hasDerivAt.comp y (hasDerivAt_neg y)).neg.deriv)
  obtain ⟨z, hz, hz_eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := F) (n := 1) (x₀ := -x) (x := 1 - x) (by linarith) hF.contDiffOn
  have hi0 : iteratedDerivWithin 0 F (Set.Icc (-x) (1-x)) (-x) = iteratedDeriv 0 F (-x) :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) (hF.contDiffAt.of_le (by norm_num))
      (by constructor <;> linarith)
  have hi1 : iteratedDerivWithin 1 F (Set.Icc (-x) (1-x)) (-x) = iteratedDeriv 1 F (-x) :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) (hF.contDiffAt.of_le (by norm_num))
      (by constructor <;> linarith)
  norm_num [taylorWithinEval, taylorWithin, taylorCoeffWithin, Finset.sum_range_succ,
    hi0, hi1, iteratedDeriv_eq_iterate] at hz_eq
  simp [F, hF1, hF2] at hz_eq
  have hmono2 : StrictMono (deriv^[2] f) := by
    apply strictMono_of_deriv_pos
    simpa [Function.iterate_succ_apply] using hf'''
  have hzlt : -z < x := by linarith [hz.1]
  have hfirst : deriv f x < f x + (deriv^[2] f) x / 2 := by
    have := hmono2 hzlt
    rw [show deriv (deriv f) = deriv^[2] f by simp] at hz_eq
    linarith [hf (x - 1)]
  let G : ℝ → ℝ := fun y ↦ deriv f (-y)
  have hG : ContDiff ℝ 1 G := hc1d.comp contDiff_neg
  have hG1 (y : ℝ) : deriv G y = -(deriv^[2] f) (-y) := by
    simpa [G] using ((hd1 (-y)).hasDerivAt.comp y (hasDerivAt_neg y)).deriv
  have hGderiv : Differentiable ℝ (deriv G) := by
    rw [show deriv G = fun y ↦ -(deriv^[2] f) (-y) from funext hG1]
    fun_prop
  have hGwithin : DifferentiableOn ℝ
      (iteratedDerivWithin 1 G (Set.Icc (-x) (2-x))) (Set.Ioo (-x) (2-x)) := by
    apply hGderiv.differentiableOn.congr
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
      (hG.contDiffAt.of_le (by norm_num)) (by constructor <;> linarith [hy.1, hy.2])]
    exact congrFun iteratedDeriv_one y
  obtain ⟨w, hw, hw_eq⟩ := taylor_mean_remainder_lagrange
    (f := G) (n := 1) (x₀ := -x) (x := 2-x) (by linarith) hG.contDiffOn hGwithin
  have hG2 (y : ℝ) : deriv (deriv G) y = (deriv^[3] f) (-y) := by
    rw [show deriv G = fun t ↦ -(deriv^[2] f) (-t) from funext hG1]
    simpa [Function.iterate_succ_apply] using
      (((hd2 (-y)).hasDerivAt.comp y (hasDerivAt_neg y)).neg.deriv)
  have hSw : Set.Icc (-x) (2-x) ∈ nhds w := Icc_mem_nhds_iff.mpr hw
  have hevent : (fun y ↦ derivWithin G (Set.Icc (-x) (2-x)) y) =ᶠ[nhds w] deriv G := by
    filter_upwards [isOpen_Ioo.mem_nhds hw] with y hy
    exact derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hy)
  have hrem : iteratedDerivWithin 2 G (Set.Icc (-x) (2-x)) w = (deriv^[3] f) (-w) := by
    rw [iteratedDerivWithin_eq_iterate]
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    rw [derivWithin_of_mem_nhds hSw, hevent.deriv_eq]
    exact hG2 w
  have hj0 : iteratedDerivWithin 0 G (Set.Icc (-x) (2-x)) (-x) = iteratedDeriv 0 G (-x) :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
      (hG.contDiffAt.of_le (by norm_num)) (by constructor <;> linarith)
  have hj1 : iteratedDerivWithin 1 G (Set.Icc (-x) (2-x)) (-x) = iteratedDeriv 1 G (-x) :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
      (hG.contDiffAt.of_le (by norm_num)) (by constructor <;> linarith)
  norm_num [taylorWithinEval, taylorWithin, taylorCoeffWithin, Finset.sum_range_succ,
    hj0, hj1, iteratedDeriv_eq_iterate, hrem] at hw_eq
  simp [G, hG1] at hw_eq
  change deriv f (x - 2) - (deriv f x - 2 * (deriv^[2] f) x) =
    (deriv^[3] f) (-w) * 4 / 2 at hw_eq
  have hmono0 : StrictMono f := strictMono_of_deriv_pos hf'
  have hwlt : -w < x := by linarith [hw.1]
  have hsecond : (deriv^[2] f) x < deriv f x / 2 + f x := by
    have hfx := hmono0 hwlt
    have hb := h_bound (-w)
    linarith [hf' (x - 2)]
  linarith
