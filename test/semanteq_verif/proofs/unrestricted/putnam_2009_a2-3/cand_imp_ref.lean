import Mathlib

open Topology MvPolynomial Filter Set

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_2009_a2_solution : ℝ → ℝ := fun x ↦ 2 ^ (-(1 : ℝ) / 12) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4)) ^ 2) ^ ((1 : ℝ) / 6)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∃ (I : Set ℝ) (f g h : ℝ → ℝ),
    IsOpen I ∧ 0 ∈ I ∧
    DifferentiableOn ℝ f I ∧ DifferentiableOn ℝ g I ∧ DifferentiableOn ℝ h I ∧
    (∀ x ∈ I, deriv f x = 2 * (f x)^2 * g x * h x + 1 / (g x * h x)) ∧
    (∀ x ∈ I, deriv g x = f x * (g x)^2 * h x + 4 / (f x * h x)) ∧
    (∀ x ∈ I, deriv h x = 3 * f x * g x * (h x)^2 + 1 / (f x * g x)) ∧
    f 0 = 1 ∧ g 0 = 1 ∧ h 0 = 1 ∧
    (∃ (J : Set ℝ), IsOpen J ∧ 0 ∈ J ∧ J ⊆ I ∧
      ∀ x ∈ J, f x = (2 : ℝ)^(-(1:ℝ)/12) * ((Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4))^2))^(1/6 : ℝ)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2009_a2
(f g h : ℝ → ℝ)
(a b : ℝ)
(hab : 0 ∈ Ioo a b)
(hdiff : DifferentiableOn ℝ f (Ioo a b) ∧ DifferentiableOn ℝ g (Ioo a b) ∧ DifferentiableOn ℝ h (Ioo a b))
(hf : (∀ x ∈ Ioo a b, deriv f x = 2 * (f x)^2 * (g x) * (h x) + 1 / ((g x) * (h x))) ∧ f 0 = 1)
(hg : (∀ x ∈ Ioo a b, deriv g x = (f x) * (g x)^2 * (h x) + 4 / ((f x) * (h x))) ∧ g 0 = 1)
(hh : (∀ x ∈ Ioo a b, deriv h x = 3 * (f x) * (g x) * (h x)^2 + 1 / ((f x) * (g x))) ∧ h 0 = 1)
: (∃ c d : ℝ, 0 ∈ Ioo c d ∧ ∀ x ∈ Ioo c d, f x = putnam_2009_a2_solution x) := by
  obtain ⟨I, F, G, H, hIopen, hI0, hFdiff, hGdiff, hHdiff,
    hFder, hGder, hHder, hF0, hG0, hH0, J, hJopen, hJ0, hJI, hformula⟩ :=
    problem_statement_assumed
  let V : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦
    (2 * p.1^2 * p.2.1 * p.2.2 + 1 / (p.2.1 * p.2.2),
      p.1 * p.2.1^2 * p.2.2 + 4 / (p.1 * p.2.2),
      3 * p.1 * p.2.1 * p.2.2^2 + 1 / (p.1 * p.2.1))
  let p : ℝ → ℝ × ℝ × ℝ := fun x ↦ (f x, g x, h x)
  let q : ℝ → ℝ × ℝ × ℝ := fun x ↦ (F x, G x, H x)
  have hV : ContDiffAt ℝ 1 V (1, 1, 1) := by
    dsimp [V]
    fun_prop (disch := norm_num)
  obtain ⟨K, s, hs, hLip⟩ := hV.exists_lipschitzOnWith
  have hpder : ∀ᶠ x in 𝓝 0, HasDerivAt p (V (p x)) x := by
    filter_upwards [Ioo_mem_nhds hab.1 hab.2] with x hx
    have hdf := (hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.congr_deriv (hf.1 x hx)
    have hdg := (hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.congr_deriv (hg.1 x hx)
    have hdh := (hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.congr_deriv (hh.1 x hx)
    exact (hdf.prodMk (hdg.prodMk hdh)).congr_deriv (by simp [p, V])
  have hqder : ∀ᶠ x in 𝓝 0, HasDerivAt q (V (q x)) x := by
    filter_upwards [hIopen.mem_nhds hI0] with x hx
    have hdF := (hFdiff.differentiableAt (hIopen.mem_nhds hx)).hasDerivAt.congr_deriv (hFder x hx)
    have hdG := (hGdiff.differentiableAt (hIopen.mem_nhds hx)).hasDerivAt.congr_deriv (hGder x hx)
    have hdH := (hHdiff.differentiableAt (hIopen.mem_nhds hx)).hasDerivAt.congr_deriv (hHder x hx)
    exact (hdF.prodMk (hdG.prodMk hdH)).congr_deriv (by simp [q, V])
  have hp0 : p 0 = ((1 : ℝ), (1 : ℝ), (1 : ℝ)) := by simp [p, hf.2, hg.2, hh.2]
  have hq0 : q 0 = ((1 : ℝ), (1 : ℝ), (1 : ℝ)) := by simp [q, hF0, hG0, hH0]
  have hpc : ContinuousAt p 0 := by
    exact (hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hab)).continuousAt.prodMk
      ((hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hab)).continuousAt.prodMk
        (hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hab)).continuousAt)
  have hqc : ContinuousAt q 0 := by
    exact (hFdiff.differentiableAt (hIopen.mem_nhds hI0)).continuousAt.prodMk
      ((hGdiff.differentiableAt (hIopen.mem_nhds hI0)).continuousAt.prodMk
        (hHdiff.differentiableAt (hIopen.mem_nhds hI0)).continuousAt)
  have hps : ∀ᶠ x in 𝓝 0, p x ∈ s := by
    apply hpc
    simpa [hp0] using hs
  have hqs : ∀ᶠ x in 𝓝 0, q x ∈ s := by
    apply hqc
    simpa [hq0] using hs
  have hpq : p =ᶠ[𝓝 0] q :=
    ODE_solution_unique_of_eventually
      (show ∀ᶠ _x : ℝ in 𝓝 0, LipschitzOnWith K V s from
        Filter.Eventually.of_forall fun _ ↦ hLip)
      (hpder.and hps) (hqder.and hqs) (hp0.trans hq0.symm)
  have hfinal : ∀ᶠ x in 𝓝 0, f x = putnam_2009_a2_solution x := by
    filter_upwards [hpq, hJopen.mem_nhds hJ0] with x heq hxJ
    calc
      f x = F x := congrArg Prod.fst heq
      _ = putnam_2009_a2_solution x := by
        simpa [putnam_2009_a2_solution] using hformula x hxJ
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hfinal
  refine ⟨-ε, ε, by simp [hε], ?_⟩
  intro x hx
  exact hball x (by simpa [Real.ball_eq_Ioo] using hx)
