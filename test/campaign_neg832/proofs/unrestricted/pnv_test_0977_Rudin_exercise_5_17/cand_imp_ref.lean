import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h : ∀ (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 → f x ∈ Set.Icc (-1: ℝ) 1) (hf : ContDiff ℝ ⊤ f) (hf₂ : f (-1) = 0) (hf₃ : f 0 = 0) (hf₄ : f 1 = 1) (hf₅ : deriv f 0 = 0) : ∃ (x : ℝ) (H : x ∈ Set.Ioo (-1: ℝ) 1), deriv (deriv (deriv f)) x ≥ 3 := by
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
  let g : ℝ → ℝ := fun x => f x - p x
  have hgdiff : DifferentiableOn ℝ g (Set.Icc (-1) 1) := by
    dsimp [g, p]
    fun_prop
  have hgm1 : g (-1) = 0 := by norm_num [g, p, hf0]
  have hg0 : g 0 = 0 := by simp [g, p, hf1]
  have hg1 : g 1 = 0 := by simp [g, p, hf2]
  obtain ⟨c, hcI, hc⟩ := exists_deriv_eq_zero (show (-1 : ℝ) < 0 by norm_num)
    (hgdiff.continuousOn.mono (Set.Icc_subset_Icc_right (by norm_num))) (hgm1.trans hg0.symm)
  obtain ⟨d, hdI, hd⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    (hgdiff.continuousOn.mono (Set.Icc_subset_Icc_left (by norm_num))) (hg0.trans hg1.symm)
  have hc_mem : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hcI.1, le_trans (le_of_lt hcI.2) (by norm_num)⟩
  have hd_mem : d ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_trans (by norm_num) (le_of_lt hdI.1), le_of_lt hdI.2⟩
  have hfc : DifferentiableAt ℝ f c := hf'.differentiableAt (Icc_mem_nhds hcI.1 (lt_trans hcI.2 (by norm_num)))
  have hfd : DifferentiableAt ℝ f d := hf'.differentiableAt (Icc_mem_nhds (lt_trans (by norm_num) hdI.1) hdI.2)
  have hc' : deriv f c - (3 * c ^ 2 + 2 * c) / 2 = 0 := by
    have hp : HasDerivAt p ((3 * c ^ 2 + 2 * c) / 2) c := by
      dsimp [p]
      convert ((hasDerivAt_pow 3 c).add (hasDerivAt_pow 2 c)).div_const 2 using 1 <;> ring
    have hg := hfc.hasDerivAt.sub hp
    change deriv (f - p) c = 0 at hc
    rw [hg.deriv] at hc
    exact hc
  have hd' : deriv f d - (3 * d ^ 2 + 2 * d) / 2 = 0 := by
    have hp : HasDerivAt p ((3 * d ^ 2 + 2 * d) / 2) d := by
      dsimp [p]
      convert ((hasDerivAt_pow 3 d).add (hasDerivAt_pow 2 d)).div_const 2 using 1 <;> ring
    have hg := hfd.hasDerivAt.sub hp
    change deriv (f - p) d = 0 at hd
    rw [hg.deriv] at hd
    exact hd
  let q : ℝ → ℝ := fun x => deriv f x - (3 * x ^ 2 + 2 * x) / 2
  have hqdiff : DifferentiableOn ℝ q (Set.Icc c d) := by
    dsimp [q]
    apply (hf''.mono ?_).sub
    · fun_prop
    · intro x hx
      exact ⟨le_trans (le_of_lt hcI.1) hx.1,
        le_trans hx.2 (le_of_lt hdI.2)⟩
  have hq0 : q 0 = 0 := by simp [q, hf3]
  have hqc : q c = 0 := hc'
  have hqd : q d = 0 := hd'
  obtain ⟨u, huI, hu⟩ := exists_deriv_eq_zero hcI.2
    (hqdiff.continuousOn.mono (Set.Icc_subset_Icc_right (le_of_lt hdI.1))) (hqc.trans hq0.symm)
  obtain ⟨v, hvI, hv⟩ := exists_deriv_eq_zero hdI.1
    (hqdiff.continuousOn.mono (Set.Icc_subset_Icc_left (le_of_lt hcI.2))) (hq0.trans hqd.symm)
  have hu_mem : u ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (le_of_lt hcI.1) (le_of_lt huI.1), le_trans (le_of_lt huI.2) (by norm_num)⟩
  have hv_mem : v ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num) (le_of_lt hvI.1), le_trans (le_of_lt hvI.2) (le_of_lt hdI.2)⟩
  have hdfu : DifferentiableAt ℝ (deriv f) u :=
    hf''.differentiableAt (Icc_mem_nhds (lt_trans hcI.1 huI.1) (lt_trans huI.2 (by norm_num)))
  have hdfv : DifferentiableAt ℝ (deriv f) v :=
    hf''.differentiableAt (Icc_mem_nhds (lt_trans (by norm_num) hvI.1) (lt_trans hvI.2 hdI.2))
  have hu' : deriv (deriv f) u - (3 * u + 1) = 0 := by
    have hp : HasDerivAt (fun x : ℝ => (3 * x ^ 2 + 2 * x) / 2) (3 * u + 1) u := by
      convert ((((hasDerivAt_const u 3).mul (hasDerivAt_pow 2 u)).add
        ((hasDerivAt_const u 2).mul (hasDerivAt_id u))).div_const 2) using 1 <;> ring
    have hq := hdfu.hasDerivAt.sub hp
    change deriv ((deriv f) - fun x : ℝ => (3 * x ^ 2 + 2 * x) / 2) u = 0 at hu
    rw [hq.deriv] at hu
    exact hu
  have hv' : deriv (deriv f) v - (3 * v + 1) = 0 := by
    have hp : HasDerivAt (fun x : ℝ => (3 * x ^ 2 + 2 * x) / 2) (3 * v + 1) v := by
      convert ((((hasDerivAt_const v 3).mul (hasDerivAt_pow 2 v)).add
        ((hasDerivAt_const v 2).mul (hasDerivAt_id v))).div_const 2) using 1 <;> ring
    have hq := hdfv.hasDerivAt.sub hp
    change deriv ((deriv f) - fun x : ℝ => (3 * x ^ 2 + 2 * x) / 2) v = 0 at hv
    rw [hq.deriv] at hv
    exact hv
  let r : ℝ → ℝ := fun x => deriv (deriv f) x - (3 * x + 1)
  have hrdiff : DifferentiableOn ℝ r (Set.Icc u v) := by
    dsimp [r]
    apply (hf'''.mono ?_).sub
    · fun_prop
    · intro x hx
      exact ⟨le_trans hu_mem.1 hx.1, le_trans hx.2 hv_mem.2⟩
  obtain ⟨x, hxI, hx⟩ := exists_deriv_eq_zero (lt_trans huI.2 hvI.1)
    hrdiff.continuousOn (hu'.trans hv'.symm)
  have hx_mem : x ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_lt hu_mem.1 hxI.1, lt_of_lt_of_le hxI.2 hv_mem.2⟩
  have hddfx : DifferentiableAt ℝ (deriv (deriv f)) x :=
    hf'''.differentiableAt (Icc_mem_nhds hx_mem.1 hx_mem.2)
  refine ⟨x, hx_mem, ?_⟩
  have : deriv (deriv (deriv f)) x - 3 = 0 := by
    have hp : HasDerivAt (fun y : ℝ => 3 * y + 1) 3 x := by
      convert ((hasDerivAt_const x 3).mul (hasDerivAt_id x)).add_const 1 using 1 <;> ring
    have hr := hddfx.hasDerivAt.sub hp
    change deriv ((deriv (deriv f)) - fun y : ℝ => 3 * y + 1) x = 0 at hx
    rw [hr.deriv] at hx
    exact hx
  linarith
