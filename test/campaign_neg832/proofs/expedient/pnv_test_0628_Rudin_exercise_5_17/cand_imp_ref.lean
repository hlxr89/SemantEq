import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h₁ : ContDiff ℝ 3 f) (h₂ : f (-1) = 0) (h₃ : f 0 = 0) (h₄ : f 1 = 1) (h₅ : deriv f 0 = 0) : ∃ x ∈ Set.Icc (-1 : ℝ) 1, deriv^[3] f x ≥ 3 := by
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
  let g : ℝ → ℝ := fun x => f x - (x ^ 3 + x ^ 2) / 2
  let q : ℝ → ℝ := fun x => deriv f x - (3 * x ^ 2 + 2 * x) / 2
  let r : ℝ → ℝ := fun x => deriv (deriv f) x - (6 * x + 2) / 2
  have hIcc_nhds {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : Set.Icc (-1 : ℝ) 1 ∈ 𝓝 x :=
    mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
  have hg_cont : ContinuousOn g (Set.Icc (-1 : ℝ) 1) := by
    apply (show DifferentiableOn ℝ g (Set.Icc (-1 : ℝ) 1) from ?_).continuousOn
    intro x hx
    exact (hf' x hx).sub (by fun_prop)
  have hg_deriv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt g (q x) x := by
    have hfx := (hf' x (Set.Ioo_subset_Icc_self hx)).differentiableAt (hIcc_nhds hx)
    have hp : HasDerivAt (fun y : ℝ => (y ^ 3 + y ^ 2) / 2)
        ((3 * x ^ 2 + 2 * x) / 2) x := by
      convert (((hasDerivAt_id x).pow 3).add ((hasDerivAt_id x).pow 2)).div_const 2 using 1 <;>
        simp only [id_eq] <;> ring
    simpa [g, q] using hfx.hasDerivAt.sub hp
  have hg_neg_one : g (-1) = g 0 := by simp [g, hf0, hf1] <;> norm_num
  have hg_zero_one : g 0 = g 1 := by simp [g, hf1, hf2]
  rcases exists_hasDerivAt_eq_zero (by norm_num : (-1 : ℝ) < 0)
      (hg_cont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])) hg_neg_one
      (fun x hx => hg_deriv ⟨by linarith [hx.1], by linarith [hx.2]⟩) with ⟨a, ha, hqa⟩
  rcases exists_hasDerivAt_eq_zero (by norm_num : (0 : ℝ) < 1)
      (hg_cont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])) hg_zero_one
      (fun x hx => hg_deriv ⟨by linarith [hx.1], by linarith [hx.2]⟩) with ⟨b, hb, hqb⟩
  have hq0 : q 0 = 0 := by simp [q, hf3]
  have hq_cont : ContinuousOn q (Set.Icc (-1 : ℝ) 1) := by
    apply (show DifferentiableOn ℝ q (Set.Icc (-1 : ℝ) 1) from ?_).continuousOn
    intro x hx
    exact (hf'' x hx).sub (by fun_prop)
  have hq_deriv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt q (r x) x := by
    have hfx := (hf'' x (Set.Ioo_subset_Icc_self hx)).differentiableAt (hIcc_nhds hx)
    have hp : HasDerivAt (fun y : ℝ => (3 * y ^ 2 + 2 * y) / 2)
        ((6 * x + 2) / 2) x := by
      convert ((((hasDerivAt_const x 3).mul ((hasDerivAt_id x).pow 2)).add
        ((hasDerivAt_const x 2).mul (hasDerivAt_id x))).div_const 2) using 1 <;>
        simp only [id_eq] <;> ring
    simpa [q, r] using hfx.hasDerivAt.sub hp
  rcases exists_hasDerivAt_eq_zero ha.2
      (hq_cont.mono (by intro x hx; constructor <;> linarith [ha.1, hx.1, hx.2])) (hqa.trans hq0.symm)
      (fun x hx => hq_deriv ⟨by linarith [ha.1, hx.1], by linarith [hx.2]⟩) with ⟨c, hc, hrc⟩
  rcases exists_hasDerivAt_eq_zero hb.1
      (hq_cont.mono (by intro x hx; constructor <;> linarith [hb.2, hx.1, hx.2])) (hq0.trans hqb.symm)
      (fun x hx => hq_deriv ⟨by linarith [hx.1], by linarith [hb.2, hx.2]⟩) with ⟨d, hd, hrd⟩
  have hr_cont : ContinuousOn r (Set.Icc (-1 : ℝ) 1) := by
    apply (show DifferentiableOn ℝ r (Set.Icc (-1 : ℝ) 1) from ?_).continuousOn
    intro x hx
    exact (hf''' x hx).sub (by fun_prop)
  have hr_deriv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt r (deriv (deriv (deriv f)) x - 3) x := by
    have hfx := (hf''' x (Set.Ioo_subset_Icc_self hx)).differentiableAt (hIcc_nhds hx)
    have hp : HasDerivAt (fun y : ℝ => (6 * y + 2) / 2) 3 x := by
      convert ((((hasDerivAt_const x 6).mul (hasDerivAt_id x)).add
        (hasDerivAt_const x 2)).div_const 2) using 1 <;>
        simp only [id_eq] <;> ring
    simpa [r] using hfx.hasDerivAt.sub hp
  rcases exists_hasDerivAt_eq_zero (by linarith [hc.2, hd.1])
      (hr_cont.mono (by intro x hx; constructor <;> linarith [ha.1, hb.2, hc.1, hd.2, hx.1, hx.2]))
      (hrc.trans hrd.symm)
      (fun x hx => hr_deriv ⟨by linarith [ha.1, hc.1, hx.1], by linarith [hb.2, hd.2, hx.2]⟩) with ⟨x, hx, hzero⟩
  exact ⟨x, ⟨by linarith [ha.1, hc.1, hx.1], by linarith [hb.2, hd.2, hx.2]⟩, by linarith⟩
