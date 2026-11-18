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
  let q : ℝ → ℝ := fun x => deriv f x - (3 * x ^ 2 + 2 * x) / 2
  let r : ℝ → ℝ := fun x => deriv (deriv f) x - (3 * x + 1)
  have hp (x : ℝ) : HasDerivAt p ((3 * x ^ 2 + 2 * x) / 2) x := by
    dsimp [p]
    convert (((hasDerivAt_id x).pow 3).add ((hasDerivAt_id x).pow 2)).div_const 2 using 1 <;> simp [id] <;> ring
  have hq (x : ℝ) : HasDerivAt (fun y : ℝ => (3 * y ^ 2 + 2 * y) / 2) (3 * x + 1) x := by
    convert (((hasDerivAt_const x 3).mul ((hasDerivAt_id x).pow 2)).add
      ((hasDerivAt_const x 2).mul (hasDerivAt_id x))).div_const 2 using 1 <;> simp [id] <;> ring
  have hr (x : ℝ) : HasDerivAt (fun y : ℝ => 3 * y + 1) 3 x := by
    convert ((hasDerivAt_const x 3).mul (hasDerivAt_id x)).add_const 1 using 1 <;> simp [id] <;> ring
  have hgdiff : DifferentiableOn ℝ (fun x => f x - p x) (Set.Icc (-1) 1) :=
    hf'.sub (fun x _ => (hp x).differentiableAt.differentiableWithinAt)
  obtain ⟨a, ha, ha0⟩ := exists_deriv_eq_zero (show (-1 : ℝ) < 0 by norm_num)
    (hgdiff.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])).continuousOn
    (by norm_num [p, hf0, hf1])
  obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    (hgdiff.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])).continuousOn
    (by simp [p, hf1, hf2])
  have hfa : DifferentiableAt ℝ f a := hf'.differentiableAt (Icc_mem_nhds (by linarith [ha.1]) (by linarith [ha.2]))
  have hfc : DifferentiableAt ℝ f c := hf'.differentiableAt (Icc_mem_nhds (by linarith [hc.1]) (by linarith [hc.2]))
  have hqa : q a = 0 := by
    calc
      q a = deriv (fun x => f x - p x) a := by
        unfold q
        symm
        convert (hfa.hasDerivAt.sub (hp a)).deriv using 1
      _ = 0 := ha0
  have hqc : q c = 0 := by
    calc
      q c = deriv (fun x => f x - p x) c := by
        unfold q
        symm
        convert (hfc.hasDerivAt.sub (hp c)).deriv using 1
      _ = 0 := hc0
  have hq0 : q 0 = 0 := by simp [q, hf3]
  have hqcont : ContinuousOn q (Set.Icc (-1) 1) :=
    hf''.continuousOn.sub (by fun_prop)
  obtain ⟨b, hb, hb0⟩ := exists_deriv_eq_zero (a := a) (b := 0) ha.2
    (hqcont.mono (by intro x hx; constructor <;> linarith [ha.1, hx.1, hx.2])) (hqa.trans hq0.symm)
  obtain ⟨d, hd, hd0⟩ := exists_deriv_eq_zero (a := 0) (b := c) hc.1
    (hqcont.mono (by intro x hx; constructor <;> linarith [hc.2, hx.1, hx.2])) (hq0.trans hqc.symm)
  have hfb : DifferentiableAt ℝ (deriv f) b := hf''.differentiableAt
    (Icc_mem_nhds (by linarith [ha.1, hb.1]) (by linarith [hb.2]))
  have hfd : DifferentiableAt ℝ (deriv f) d := hf''.differentiableAt
    (Icc_mem_nhds (by linarith [hd.1]) (by linarith [hc.2, hd.2]))
  have hrb : r b = 0 := by
    calc
      r b = deriv q b := by
        unfold r q
        symm
        convert (hfb.hasDerivAt.sub (hq b)).deriv using 1
      _ = 0 := hb0
  have hrd : r d = 0 := by
    calc
      r d = deriv q d := by
        unfold r q
        symm
        convert (hfd.hasDerivAt.sub (hq d)).deriv using 1
      _ = 0 := hd0
  have hrcont : ContinuousOn r (Set.Icc (-1) 1) :=
    hf'''.continuousOn.sub (by fun_prop)
  obtain ⟨x, hx, hx0⟩ := exists_deriv_eq_zero (a := b) (b := d) (by linarith [hb.2, hd.1])
    (hrcont.mono (by intro y hy; constructor <;> linarith [ha.1, hb.1, hc.2, hd.2, hy.1, hy.2]))
    (hrb.trans hrd.symm)
  have hfx : DifferentiableAt ℝ (deriv (deriv f)) x := hf'''.differentiableAt
    (Icc_mem_nhds (by linarith [ha.1, hb.1, hx.1]) (by linarith [hc.2, hd.2, hx.2]))
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · linarith [ha.1, hb.1, hx.1]
  · linarith [hc.2, hd.2, hx.2]
  have hxder : deriv r x = deriv (deriv (deriv f)) x - 3 := by
    unfold r
    convert (hfx.hasDerivAt.sub (hr x)).deriv using 1
  rw [hxder] at hx0
  linarith
