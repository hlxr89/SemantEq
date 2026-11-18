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
theorem dummy {f : ℝ → ℝ} (hf_pos : ∀ x, 0 < f x) (hf_cont : Continuous f) (hf_deriv_pos : ∀ x, 0 < deriv f x) (hf_deriv2_pos : ∀ x, 0 < deriv^[2] f x) (hf_deriv3_pos : ∀ x, 0 < deriv^[3] f x) (hf_deriv3_le_fun : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  have hd0 : Differentiable ℝ f := fun z =>
    differentiableAt_of_deriv_ne_zero (ne_of_gt (hf_deriv_pos z))
  have hd1 : Differentiable ℝ (deriv f) := fun z =>
    differentiableAt_of_deriv_ne_zero (ne_of_gt (by
      simpa [Function.iterate_succ_apply'] using hf_deriv2_pos z))
  have hd2 : Differentiable ℝ (deriv (deriv f)) := fun z =>
    differentiableAt_of_deriv_ne_zero (ne_of_gt (by
      simpa [Function.iterate_succ_apply'] using hf_deriv3_pos z))
  have hmono : StrictMono f := strictMono_of_deriv_pos hf_deriv_pos
  intro x
  let a := f x
  let b := deriv f x
  let c := deriv (deriv f) x
  have ha : 0 < a := hf_pos x
  have hb : 0 < b := hf_deriv_pos x
  have hc : 0 < c := by
    simpa [c, Function.iterate_succ_apply'] using hf_deriv2_pos x
  let H₂ : ℝ → ℝ := fun y => c - deriv (deriv f) y
  let H₁ : ℝ → ℝ := fun y => b + c * (y - x) - deriv f y
  let H₀ : ℝ → ℝ := fun y => a + b * (y - x) + c / 2 * (y - x)^2 - f y
  have dH₂ : ∀ y, HasDerivAt H₂ (-deriv (deriv (deriv f)) y) y := by
    intro y
    dsimp [H₂]
    convert (hasDerivAt_const y c).sub (hd2 y).hasDerivAt using 1 <;> ring
  have dH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y := by
    intro y
    dsimp [H₁, H₂]
    convert (((hasDerivAt_const y b).add
      ((hasDerivAt_const y c).mul ((hasDerivAt_id y).sub_const x))).sub
        (hd1 y).hasDerivAt) using 1 <;> simp [id] <;> ring
  have dH₀ : ∀ y, HasDerivAt H₀ (H₁ y) y := by
    intro y
    dsimp [H₀, H₁]
    convert (((hasDerivAt_const y a).add
      ((hasDerivAt_const y b).mul ((hasDerivAt_id y).sub_const x))).add
      (((hasDerivAt_const y (c/2)).mul (((hasDerivAt_id y).sub_const x).pow 2)))).sub
        (hd0 y).hasDerivAt using 1 <;> simp [id] <;> ring
  have H₂pos : ∀ y < x, 0 < H₂ y := by
    intro y hy
    have hanti : StrictAnti H₂ := strictAnti_of_deriv_neg fun z => by
      rw [(dH₂ z).deriv]
      have := hf_deriv3_pos z
      simpa [Function.iterate_succ_apply'] using (neg_neg_of_pos this)
    have := hanti hy
    simpa [H₂, c] using this
  have H₁neg : ∀ y < x, H₁ y < 0 := by
    intro y hy
    have hm : StrictMonoOn H₁ (Set.Iic x) :=
      strictMonoOn_of_deriv_pos (convex_Iic x)
        (fun z _ => (dH₁ z).continuousAt.continuousWithinAt)
        (fun z hz => by
          rw [(dH₁ z).deriv]
          exact H₂pos z (by simpa using hz))
    have := hm (show y ∈ Set.Iic x from hy.le) (show x ∈ Set.Iic x by simp) hy
    simpa [H₁, b, c] using this
  have H₀pos : ∀ y < x, 0 < H₀ y := by
    intro y hy
    have ha' : StrictAntiOn H₀ (Set.Iic x) :=
      strictAntiOn_of_deriv_neg (convex_Iic x)
        (fun z _ => (dH₀ z).continuousAt.continuousWithinAt)
        (fun z hz => by
          rw [(dH₀ z).deriv]
          exact H₁neg z (by simpa using hz))
    have := ha' (show y ∈ Set.Iic x from hy.le) (show x ∈ Set.Iic x by simp) hy
    have hx0 : H₀ x = 0 := by simp [H₀, a]
    linarith
  have hquad1 : 0 < a - b^2 / (2*c) := by
    have harg : x - b/c < x := sub_lt_self x (div_pos hb hc)
    have := H₀pos (x - b/c) harg
    have hypos := hf_pos (x - b/c)
    have heq : a - b^2 / (2*c) =
        a + b * ((x - b/c) - x) + c / 2 * ((x - b/c) - x)^2 := by
      field_simp
      ring
    dsimp [H₀] at this
    rw [heq]
    linarith
  let K₁ : ℝ → ℝ := fun y => c + a * (y - x) - deriv (deriv f) y
  let K₀ : ℝ → ℝ := fun y => b + c * (y - x) + a / 2 * (y - x)^2 - deriv f y
  have dK₁ : ∀ y, HasDerivAt K₁ (a - deriv (deriv (deriv f)) y) y := by
    intro y
    dsimp [K₁]
    convert (((hasDerivAt_const y c).add
      ((hasDerivAt_const y a).mul ((hasDerivAt_id y).sub_const x))).sub
        (hd2 y).hasDerivAt) using 1 <;> simp [id] <;> ring
  have dK₀ : ∀ y, HasDerivAt K₀ (K₁ y) y := by
    intro y
    dsimp [K₀, K₁]
    convert (((hasDerivAt_const y b).add
      ((hasDerivAt_const y c).mul ((hasDerivAt_id y).sub_const x))).add
      (((hasDerivAt_const y (a/2)).mul (((hasDerivAt_id y).sub_const x).pow 2)))).sub
        (hd1 y).hasDerivAt using 1 <;> simp [id] <;> ring
  have K₁nonpos : ∀ y < x, K₁ y ≤ 0 := by
    intro y hy
    have hm : MonotoneOn K₁ (Set.Iic x) :=
      monotoneOn_of_deriv_nonneg (convex_Iic x)
        (fun z _ => (dK₁ z).continuousAt.continuousWithinAt)
        (fun z _ => (dK₁ z).differentiableAt.differentiableWithinAt)
        (fun z hz => by
          rw [(dK₁ z).deriv]
          have hzx : z < x := by simpa using hz
          have hle : deriv (deriv (deriv f)) z ≤ f z := by
            simpa [Function.iterate_succ_apply'] using hf_deriv3_le_fun z
          dsimp [a]
          linarith [hle.trans (hmono.monotone hzx.le)])
    have := hm (show y ∈ Set.Iic x from hy.le) (show x ∈ Set.Iic x by simp) hy.le
    simpa [K₁, a, c] using this
  have K₀nonneg : ∀ y < x, 0 ≤ K₀ y := by
    intro y hy
    have ha' : AntitoneOn K₀ (Set.Iic x) :=
      antitoneOn_of_deriv_nonpos (convex_Iic x)
        (fun z _ => (dK₀ z).continuousAt.continuousWithinAt)
        (fun z _ => (dK₀ z).differentiableAt.differentiableWithinAt)
        (fun z hz => by
          rw [(dK₀ z).deriv]
          exact K₁nonpos z (by simpa using hz))
    have := ha' (show y ∈ Set.Iic x from hy.le) (show x ∈ Set.Iic x by simp) hy.le
    simpa [K₀, b, c] using this
  have hquad2 : 0 < b - c^2 / (2*a) := by
    have harg : x - c/a < x := sub_lt_self x (div_pos hc ha)
    have hk := K₀nonneg (x - c/a) harg
    have hp := hf_deriv_pos (x - c/a)
    have heq : b - c^2 / (2*a) =
        b + c * ((x - c/a) - x) + a / 2 * ((x - c/a) - x)^2 := by
      field_simp
      ring
    dsimp [K₀] at hk
    rw [heq]
    linarith
  field_simp at hquad1 hquad2
  have hp1 : 0 < (2*a*c - b^2) * (2*a*c + b^2) :=
    mul_pos (by nlinarith) (by positivity)
  have hp2 : 0 < 4*a^2 * (2*a*b - c^2) :=
    mul_pos (by positivity) (by nlinarith)
  have hcubes : b^3 < 8*a^3 := by nlinarith
  by_contra hn
  have hba : 0 ≤ b - 2*a := by linarith
  have hfac : 0 ≤ (b - 2*a) * (b^2 + 2*a*b + 4*a^2) :=
    mul_nonneg hba (by nlinarith [sq_nonneg (b+a)])
  nlinarith
