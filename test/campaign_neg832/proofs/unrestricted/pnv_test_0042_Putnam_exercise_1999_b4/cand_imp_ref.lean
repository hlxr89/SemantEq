import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ x, f x > 0) (hf' : ∀ x, HasDerivAt f (f x) x) (hf'' : ∀ x, HasDerivAt (deriv f) (deriv f x) x) (hf''' : ∀ x, HasDerivAt (deriv (deriv f)) (deriv (deriv f) x) x) (h : ∀ x, (deriv (deriv (deriv f))) x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  intro x
  have ha : 0 < f x := by simpa using hf1 0 (by omega) x
  have hb : 0 < iteratedDeriv 1 f x := hf1 1 (by omega) x
  have hc : 0 < iteratedDeriv 2 f x := hf1 2 (by omega) x
  have hmono : StrictMono f := strictMono_of_deriv_pos (fun y => by
    simpa [iteratedDeriv_one] using hf1 1 (by omega) y)
  have habc : (iteratedDeriv 1 f x)^2 < 2 * f x * iteratedDeriv 2 f x := by
    let t := iteratedDeriv 1 f x / iteratedDeriv 2 f x
    have ht : 0 < t := div_pos hb hc
    let g : ℝ → ℝ := fun s => f (x - s)
    have hg : ContDiff ℝ 3 g := by dsimp [g]; fun_prop
    obtain ⟨z, hz, hzrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) ht hg.contDiffOn
    have hpoly : taylorWithinEval g 2 (Set.Icc 0 t) 0 t =
        f x - t * iteratedDeriv 1 f x + t^2 / 2 * iteratedDeriv 2 f x := by
      rw [taylor_within_apply]
      have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) t) := uniqueDiffOn_Icc ht
      have heq (n : ℕ) (hn : n ≤ 2) :
          iteratedDerivWithin n g (Set.Icc 0 t) 0 = iteratedDeriv n g 0 := by
        apply iteratedDerivWithin_eq_iteratedDeriv hu
        · exact hg.contDiffAt.of_le (by norm_num; omega)
        · simp [ht.le]
      norm_num [Finset.sum_range_succ, heq]
      dsimp [g]
      simp only [iteratedDeriv_comp_const_sub]
      norm_num [iteratedDeriv_one, deriv_comp_const_sub]
      ring
    have hremneg : iteratedDeriv 3 g z * (t - 0) ^ (3 : ℕ) / (6 : ℝ) < 0 := by
      have hd : iteratedDeriv 3 g z = - iteratedDeriv 3 f (x-z) := by
        dsimp [g]
        rw [iteratedDeriv_comp_const_sub]
        norm_num
      rw [hd]
      have hp : 0 < iteratedDeriv 3 f (x-z) := hf1 3 (by omega) _
      have hprod : 0 < iteratedDeriv 3 f (x-z) * t^3 := mul_pos hp (pow_pos ht 3)
      norm_num
      nlinarith
    have hgt : 0 < g t := by dsimp [g]; exact hf1 0 (by omega) _
    have hP : 0 < f x - t * iteratedDeriv 1 f x + t^2 / 2 * iteratedDeriv 2 f x := by
      rw [← hpoly]
      rw [hpoly] at hzrem
      norm_num only [Nat.factorial, Nat.cast_ofNat, add_zero, sub_zero] at hzrem
      nlinarith
    dsimp [t] at hP
    field_simp at hP ⊢
    nlinarith [sq_pos_of_pos hc]
  have hacb : (iteratedDeriv 2 f x)^2 < 2 * f x * iteratedDeriv 1 f x := by
    let t := iteratedDeriv 2 f x / f x
    have ht : 0 < t := div_pos hc ha
    let g : ℝ → ℝ := fun s => iteratedDeriv 1 f (x - s)
    have hfderiv : ContDiff ℝ 2 (deriv f) := by
      apply (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) f by norm_num; exact hf)).2.2
    have hf1cd : ContDiff ℝ 2 (iteratedDeriv 1 f) := by
      simpa [iteratedDeriv_one] using hfderiv
    have hg : ContDiff ℝ 2 g := by dsimp [g]; fun_prop
    obtain ⟨z, hz, hzrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) ht hg.contDiffOn
    have hpoly : taylorWithinEval g 1 (Set.Icc 0 t) 0 t =
        iteratedDeriv 1 f x - t * iteratedDeriv 2 f x := by
      rw [taylor_within_apply]
      have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) t) := uniqueDiffOn_Icc ht
      have heq (n : ℕ) (hn : n ≤ 1) :
          iteratedDerivWithin n g (Set.Icc 0 t) 0 = iteratedDeriv n g 0 := by
        apply iteratedDerivWithin_eq_iteratedDeriv hu
        · exact hg.contDiffAt.of_le (by norm_num; omega)
        · simp [ht.le]
      norm_num [Finset.sum_range_succ, heq]
      dsimp [g]
      norm_num [iteratedDeriv_one, deriv_comp_const_sub, iteratedDeriv_succ]
      ring
    have hgz : iteratedDeriv 2 g z = iteratedDeriv 3 f (x-z) := by
      dsimp [g]
      rw [iteratedDeriv_comp_const_sub]
      norm_num [iteratedDeriv_succ]
    have hfxz : f (x-z) < f x := hmono (sub_lt_self x hz.1)
    have hrembd : iteratedDeriv 2 g z * (t - 0) ^ (2 : ℕ) / (2 : ℝ) <
        f x * t^2 / 2 := by
      rw [hgz]
      have := hf2 (x-z)
      have ht2 : 0 < t^2 := sq_pos_of_pos ht
      norm_num
      nlinarith
    have hgt : 0 < g t := by dsimp [g]; exact hf1 1 (by omega) _
    have hP : 0 < iteratedDeriv 1 f x - t * iteratedDeriv 2 f x + f x * t^2 / 2 := by
      rw [hpoly] at hzrem
      norm_num only [Nat.factorial, Nat.cast_ofNat, add_zero, sub_zero] at hzrem
      nlinarith
    dsimp [t] at hP
    field_simp at hP ⊢
    nlinarith [sq_pos_of_pos ha]
  rw [← iteratedDeriv_one]
  by_contra hn
  have htwo : 2 * f x ≤ iteratedDeriv 1 f x := le_of_not_gt hn
  nlinarith [sq_nonneg ((iteratedDeriv 1 f x)^2),
    sq_nonneg ((iteratedDeriv 2 f x)^2),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
