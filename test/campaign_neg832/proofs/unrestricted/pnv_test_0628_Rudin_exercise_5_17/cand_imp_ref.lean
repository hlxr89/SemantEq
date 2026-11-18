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
  let p : ℝ → ℝ := fun x => (x ^ 3 + x ^ 2) / 2
  let p₁ : ℝ → ℝ := fun x => (3 * x ^ 2 + 2 * x) / 2
  let p₂ : ℝ → ℝ := fun x => (6 * x + 2) / 2
  let g₀ : ℝ → ℝ := fun x => f x - p x
  let g₁ : ℝ → ℝ := fun x => deriv f x - p₁ x
  let g₂ : ℝ → ℝ := fun x => deriv (deriv f) x - p₂ x

  have hp₀ (x : ℝ) : HasDerivAt p (p₁ x) x := by
    dsimp [p, p₁]
    convert ((((hasDerivAt_id x).pow 3).add ((hasDerivAt_id x).pow 2)).div_const 2) using 1 <;>
      simp [id_eq] <;> ring
  have hp₁ (x : ℝ) : HasDerivAt p₁ (p₂ x) x := by
    dsimp [p₁, p₂]
    convert (((((hasDerivAt_id x).pow 2).const_mul 3).add
      ((hasDerivAt_id x).const_mul 2)).div_const 2) using 1 <;> simp [id_eq] <;> ring
  have hp₂ (x : ℝ) : HasDerivAt p₂ 3 x := by
    dsimp [p₂]
    convert ((((hasDerivAt_id x).const_mul 6).add_const 2).div_const 2) using 1 <;> ring

  have hIoo_at_f {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : DifferentiableAt ℝ f x :=
    ((hf'.mono Set.Ioo_subset_Icc_self) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hIoo_at_df {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
      DifferentiableAt ℝ (deriv f) x :=
    ((hf''.mono Set.Ioo_subset_Icc_self) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hIoo_at_ddf {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
      DifferentiableAt ℝ (deriv (deriv f)) x :=
    ((hf'''.mono Set.Ioo_subset_Icc_self) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)

  have hg₀_deriv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : deriv g₀ x = g₁ x := by
    dsimp [g₀, g₁]
    exact ((hIoo_at_f hx).hasDerivAt.sub (hp₀ x)).deriv
  have hg₁_deriv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : deriv g₁ x = g₂ x := by
    dsimp [g₁, g₂]
    exact ((hIoo_at_df hx).hasDerivAt.sub (hp₁ x)).deriv
  have hg₂_deriv {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
      deriv g₂ x = deriv (deriv (deriv f)) x - 3 := by
    dsimp [g₂]
    exact ((hIoo_at_ddf hx).hasDerivAt.sub (hp₂ x)).deriv

  have hg₀_cont : ContinuousOn g₀ (Set.Icc (-1 : ℝ) 1) := by
    dsimp only [g₀]
    exact hf'.continuousOn.sub (by dsimp [p]; fun_prop)
  have hg₁_cont : ContinuousOn g₁ (Set.Icc (-1 : ℝ) 1) := by
    dsimp only [g₁]
    exact hf''.continuousOn.sub (by dsimp [p₁]; fun_prop)
  have hg₂_cont : ContinuousOn g₂ (Set.Icc (-1 : ℝ) 1) := by
    dsimp only [g₂]
    exact hf'''.continuousOn.sub (by dsimp [p₂]; fun_prop)

  have hg₀m : g₀ (-1) = 0 := by dsimp [g₀, p]; rw [hf0]; norm_num
  have hg₀z : g₀ 0 = 0 := by dsimp [g₀, p]; rw [hf1]; norm_num
  have hg₀p : g₀ 1 = 0 := by dsimp [g₀, p]; rw [hf2]; norm_num
  have hg₁z : g₁ 0 = 0 := by dsimp [g₁, p₁]; rw [hf3]; norm_num

  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero (show (-1 : ℝ) < 0 by norm_num)
    (hg₀_cont.mono (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩))
    (hg₀m.trans hg₀z.symm)
  obtain ⟨d, hd, hdd⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    (hg₀_cont.mono (by intro x hx; exact ⟨(by linarith [hx.1]), hx.2⟩))
    (hg₀z.trans hg₀p.symm)
  have hcI : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hc.1, hc.2.trans (by norm_num)⟩
  have hdI : d ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(by norm_num : (-1 : ℝ) < 0).trans hd.1, hd.2⟩
  have hg₁c : g₁ c = 0 := (hg₀_deriv hcI).symm.trans hdc
  have hg₁d : g₁ d = 0 := (hg₀_deriv hdI).symm.trans hdd

  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_zero hc.2
    (hg₁_cont.mono (Set.Icc_subset_Icc (le_of_lt hc.1) (by norm_num)))
    (hg₁c.trans hg₁z.symm)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hd.1
    (hg₁_cont.mono (Set.Icc_subset_Icc (by norm_num) (le_of_lt hd.2)))
    (hg₁z.trans hg₁d.symm)
  have huI : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hc.1.trans hu.1, hu.2.trans (by norm_num)⟩
  have hvI : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨(by norm_num : (-1 : ℝ) < 0).trans hv.1, hv.2.trans hd.2⟩
  have hg₂u : g₂ u = 0 := (hg₁_deriv huI).symm.trans hdu
  have hg₂v : g₂ v = 0 := (hg₁_deriv hvI).symm.trans hdv

  have huv : u < v := hu.2.trans hv.1
  obtain ⟨x, hx, hdx⟩ := exists_deriv_eq_zero huv
    (hg₂_cont.mono (Set.Icc_subset_Icc (le_trans (le_of_lt hc.1) (le_of_lt hu.1))
      (le_trans (le_of_lt hv.2) (le_of_lt hd.2)))) (hg₂u.trans hg₂v.symm)
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨hc.1.trans (hu.1.trans hx.1), hx.2.trans (hv.2.trans hd.2)⟩
  refine ⟨x, hxI, ?_⟩
  have := hg₂_deriv hxI
  rw [hdx] at this
  linarith
