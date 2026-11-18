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
set_option maxHeartbeats 800000 in
theorem dummy {f : ℝ → ℝ} (hf_pos : ∀ x, 0 < f x) (hf_cont : Continuous f) (hf_deriv_pos : ∀ x, 0 < deriv f x) (hf_deriv2_pos : ∀ x, 0 < deriv^[2] f x) (hf_deriv3_pos : ∀ x, 0 < deriv^[3] f x) (hf_deriv3_le_fun : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  have hd0 : Differentiable ℝ f := fun x => differentiableAt_of_deriv_ne_zero (hf_deriv_pos x).ne'
  have hd1 : Differentiable ℝ (deriv f) := fun x =>
    differentiableAt_of_deriv_ne_zero (by simpa [Function.iterate_succ_apply'] using (hf_deriv2_pos x).ne')
  have hd2 : Differentiable ℝ (deriv^[2] f) := fun x =>
    differentiableAt_of_deriv_ne_zero (by simpa [Function.iterate_succ_apply'] using (hf_deriv3_pos x).ne')
  have hcf2 : ContDiff ℝ 2 f := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
    exact ⟨hd0, by simp, contDiff_one_iff_deriv.mpr ⟨hd1, hd2.continuous⟩⟩
  intro x
  let d0 := f x
  let d1 := deriv f x
  let d2 := deriv^[2] f x
  have hd0p : 0 < d0 := hf_pos x
  have hd1p : 0 < d1 := hf_deriv_pos x
  have hd2p : 0 < d2 := hf_deriv2_pos x
  let a := x - d1 / d2
  have hax : a < x := by
    dsimp [a]
    have : 0 < d1 / d2 := div_pos hd1p hd2p
    linarith
  have href : ContDiff ℝ 2 (fun z : ℝ => f (-z)) := hcf2.comp contDiff_neg
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun z : ℝ => f (-z)) (n := 1) (x₀ := -x) (x := -a) (by linarith) href.contDiffOn
  have hu : UniqueDiffOn ℝ (Set.Icc (-x) (-a)) := uniqueDiffOn_Icc (by linarith)
  have hbridge : iteratedDerivWithin 1 (fun z : ℝ => f (-z)) (Set.Icc (-x) (-a)) (-x) =
      iteratedDeriv 1 (fun z : ℝ => f (-z)) (-x) :=
    iteratedDerivWithin_eq_iteratedDeriv hu (href.contDiffAt.of_le (by norm_num)) (by constructor <;> linarith)
  rw [taylor_within_apply] at heq
  norm_num [Finset.sum_range_succ, hbridge, iteratedDerivWithin_zero, iteratedDeriv_zero] at heq
  have hrefl1 : deriv (fun z : ℝ => f (-z)) (-x) = -deriv f x := by
    simpa [iteratedDeriv_one] using iteratedDeriv_comp_neg 1 f (-x)
  have hrefl2 : iteratedDeriv 2 (fun z : ℝ => f (-z)) y = deriv^[2] f (-y) := by
    simpa [iteratedDeriv_eq_iterate] using iteratedDeriv_comp_neg 2 f y
  have ht : -a + x = d1 / d2 := by dsimp [a]; ring
  rw [hrefl1, hrefl2, ht] at heq
  have hmono2 : StrictMono (deriv^[2] f) := strictMono_of_deriv_pos (fun z => by
    simpa [Function.iterate_succ_apply'] using hf_deriv3_pos z)
  have hrem : deriv^[2] f (-y) < d2 := by
    apply hmono2
    dsimp [d2]
    linarith [hy.1]
  have hfa := hf_pos a
  have hrem' : deriv (deriv f) (-y) < d2 := by
    simpa [Function.iterate_succ_apply'] using hrem
  field_simp [ne_of_gt hd2p] at heq
  have hsquare : 0 ≤ d1 ^ 2 := sq_nonneg d1
  have hsquare2 : 0 ≤ d2 ^ 2 := sq_nonneg d2
  have hmul := mul_lt_mul_of_pos_left hrem' (sq_pos_of_pos hd1p)
  have hfamul : 0 < f a * d2 ^ 2 := mul_pos hfa (sq_pos_of_pos hd2p)
  have hineq : d1 ^ 2 < 2 * d0 * d2 := by
    dsimp [d0, d1] at heq ⊢
    nlinarith
  let b := x - d2 / d0
  have hbx : b < x := by
    dsimp [b]
    have : 0 < d2 / d0 := div_pos hd2p hd0p
    linarith
  let g : ℝ → ℝ := deriv f
  let gr : ℝ → ℝ := fun z => g (-z)
  have hcg1 : ContDiff ℝ 1 g := by
    exact contDiff_one_iff_deriv.mpr ⟨hd1, hd2.continuous⟩
  have hcgr1 : ContDiff ℝ 1 gr := hcg1.comp contDiff_neg
  have hbg : -x < -b := by linarith
  let S := Set.Icc (-x) (-b)
  let U := Set.Ioo (-x) (-b)
  have hu2 : UniqueDiffOn ℝ S := uniqueDiffOn_Icc hbg
  have heqOn : Set.EqOn (iteratedDerivWithin 1 gr S) (iteratedDeriv 1 gr) U := by
    intro z hz
    exact iteratedDerivWithin_eq_iteratedDeriv hu2 (hcgr1.contDiffAt) ⟨hz.1.le, hz.2.le⟩
  have hdg2 : Differentiable ℝ (deriv g) := by
    dsimp [g]
    simpa [Function.iterate_succ_apply'] using hd2
  have hdir1 : Differentiable ℝ (iteratedDeriv 1 gr) := by
    have he : iteratedDeriv 1 gr = fun z => -(iteratedDeriv 1 g (-z)) := by
      funext z
      simpa [gr] using iteratedDeriv_comp_neg 1 g z
    rw [he]
    simpa [iteratedDeriv_one] using (hdg2.comp differentiable_neg).neg
  have hdWithin : DifferentiableOn ℝ (iteratedDerivWithin 1 gr S) U :=
    hdir1.differentiableOn.congr heqOn
  obtain ⟨z, hz, heq2⟩ := taylor_mean_remainder_lagrange
    (f := gr) (n := 1) (x₀ := -x) (x := -b) hbg hcgr1.contDiffOn hdWithin
  have hbridge1 : iteratedDerivWithin 1 gr S (-x) = iteratedDeriv 1 gr (-x) :=
    iteratedDerivWithin_eq_iteratedDeriv hu2 hcgr1.contDiffAt ⟨le_rfl, hbg.le⟩
  have hrembridge : iteratedDerivWithin 2 gr S z = iteratedDeriv 2 gr z := by
    rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ, iteratedDeriv_succ]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hz)]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
    exact heqOn hw
  rw [taylor_within_apply] at heq2
  norm_num [Finset.sum_range_succ, S, hbridge1, iteratedDerivWithin_zero,
    iteratedDeriv_zero] at heq2
  have hgr1 : deriv gr (-x) = -deriv g x := by
    simpa [gr, iteratedDeriv_one] using iteratedDeriv_comp_neg 1 g (-x)
  have hgr2 : iteratedDerivWithin 2 gr S z = deriv^[3] f (-z) := by
    rw [hrembridge]
    simpa [gr, g, iteratedDeriv_eq_iterate] using iteratedDeriv_comp_neg 2 g z
  have ht2 : -b + x = d2 / d0 := by dsimp [b]; ring
  rw [hgr1, hgr2, ht2] at heq2
  have hmono0 : StrictMono f := strictMono_of_deriv_pos hf_deriv_pos
  have hthird : deriv^[3] f (-z) < d0 := lt_of_le_of_lt (hf_deriv3_le_fun (-z)) (by
    dsimp [d0]
    apply hmono0
    linarith [hz.1])
  have hfb := hf_deriv_pos b
  have hthirdmul := mul_lt_mul_of_pos_left hthird (sq_pos_of_pos hd2p)
  have hgb : gr (-b) = deriv f b := by simp [gr, g]
  have hgx : gr (-x) = deriv f x := by simp [gr, g]
  have hgd : deriv g x = d2 := by
    simp [g, d2, Function.iterate_succ_apply']
  have hfd : deriv (deriv f) x = d2 := by
    simp [d2, Function.iterate_succ_apply']
  have hfdd : deriv (deriv (deriv f)) (-z) = deriv^[3] f (-z) := by
    simp [Function.iterate_succ_apply']
  field_simp [ne_of_gt hd0p] at heq2
  have hfbmul : 0 < deriv f b * d0 ^ 2 := mul_pos hfb (sq_pos_of_pos hd0p)
  have hineq2 : d2 ^ 2 < 2 * d1 * d0 := by
    dsimp [d1, d2] at heq2 ⊢
    nlinarith
  have hi1sq : d1 ^ 4 < (2 * d0 * d2) ^ 2 := by
    have hh := mul_lt_mul hineq hineq.le (sq_pos_of_pos hd1p) (by positivity)
    nlinarith only [hh]
  have hi2mul : 4 * d0 ^ 2 * d2 ^ 2 < 4 * d0 ^ 2 * (2 * d1 * d0) :=
    mul_lt_mul_of_pos_left hineq2 (by positivity)
  have hcubic : d1 ^ 3 < 8 * d0 ^ 3 := by
    have hd14 : d1 ^ 4 < 8 * d0 ^ 3 * d1 := by nlinarith
    by_contra hn
    push_neg at hn
    have hm := mul_le_mul_of_nonneg_right hn hd1p.le
    nlinarith
  apply (show Odd 3 by decide).strictMono_pow.lt_iff_lt.mp
  convert hcubic using 1 <;> dsimp [d0, d1] <;> ring
