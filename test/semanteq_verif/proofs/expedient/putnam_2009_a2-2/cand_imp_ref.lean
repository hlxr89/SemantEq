import Mathlib

open Topology MvPolynomial Filter Set

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_2009_a2_solution : ℝ → ℝ := fun x ↦ 2 ^ (-(1 : ℝ) / 12) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4)) ^ 2) ^ ((1 : ℝ) / 6)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∃ (f g h : ℝ → ℝ) (I : Set ℝ),
    IsOpen I ∧
    (0 : ℝ) ∈ I ∧
    DifferentiableOn ℝ f I ∧
    DifferentiableOn ℝ g I ∧
    DifferentiableOn ℝ h I ∧
    (∀ x ∈ I, f x ≠ 0 ∧ g x ≠ 0 ∧ h x ≠ 0) ∧
    (∀ x ∈ I, deriv f x = 2 * (f x)^2 * g x * h x + 1 / (g x * h x)) ∧
    (∀ x ∈ I, deriv g x = f x * (g x)^2 * h x + 4 / (f x * h x)) ∧
    (∀ x ∈ I, deriv h x = 3 * f x * g x * (h x)^2 + 1 / (f x * g x)) ∧
    f 0 = 1 ∧
    g 0 = 1 ∧
    h 0 = 1 ∧
    (∀ x ∈ I, f x = (2 : ℝ)^(-1/12 : ℝ) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4))^2)^(1/6 : ℝ)) := by
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
  obtain ⟨F, G, H, I, hIo, h0I, hFd, hGd, hHd, hnz, hF', hG', hH', hF0, hG0, hH0, hformula⟩ :=
    problem_statement_assumed
  let V : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦
    (2 * p.1 ^ 2 * p.2.1 * p.2.2 + 1 / (p.2.1 * p.2.2),
      p.1 * p.2.1 ^ 2 * p.2.2 + 4 / (p.1 * p.2.2),
      3 * p.1 * p.2.1 * p.2.2 ^ 2 + 1 / (p.1 * p.2.1))
  have hV : ContDiffAt ℝ 1 V (1, 1, 1) := by
    dsimp [V]
    fun_prop (disch := norm_num)
  obtain ⟨K, s, hs, hVs⟩ := hV.exists_lipschitzOnWith
  let α : ℝ → ℝ × ℝ × ℝ := fun x ↦ (f x, g x, h x)
  let β : ℝ → ℝ × ℝ × ℝ := fun x ↦ (F x, G x, H x)
  have hα0 : α 0 = (1, 1, 1) := by simp [α, hf.2, hg.2, hh.2]
  have hβ0 : β 0 = (1, 1, 1) := by simp [β, hF0, hG0, hH0]
  have hαc : ContinuousAt α 0 := by
    have hfc := (hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hab)).continuousAt
    have hgc := (hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hab)).continuousAt
    have hhc := (hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hab)).continuousAt
    exact hfc.prodMk (hgc.prodMk hhc)
  have hβc : ContinuousAt β 0 := by
    have hfc := (hFd.differentiableAt (hIo.mem_nhds h0I)).continuousAt
    have hgc := (hGd.differentiableAt (hIo.mem_nhds h0I)).continuousAt
    have hhc := (hHd.differentiableAt (hIo.mem_nhds h0I)).continuousAt
    exact hfc.prodMk (hgc.prodMk hhc)
  have hαder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt α (V (α x)) x := by
    have h1 := (hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have h2 := (hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have h3 := (hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    rw [hf.1 x hx] at h1
    rw [hg.1 x hx] at h2
    rw [hh.1 x hx] at h3
    simpa [α, V] using h1.prodMk (h2.prodMk h3)
  have hβder (x : ℝ) (hx : x ∈ I) : HasDerivAt β (V (β x)) x := by
    have h1 := (hFd.differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have h2 := (hGd.differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    have h3 := (hHd.differentiableAt (hIo.mem_nhds hx)).hasDerivAt
    rw [hF' x hx] at h1
    rw [hG' x hx] at h2
    rw [hH' x hx] at h3
    simpa [β, V] using h1.prodMk (h2.prodMk h3)
  have hsα : s ∈ 𝓝 (α 0) := by rw [hα0]; exact hs
  have hsβ : s ∈ 𝓝 (β 0) := by rw [hβ0]; exact hs
  have hαev : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt α (V (α x)) x ∧ α x ∈ s := by
    filter_upwards [Ioo_mem_nhds hab.1 hab.2, hαc.tendsto hsα] with x hx hxs
    exact ⟨hαder x hx, hxs⟩
  have hβev : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt β (V (β x)) x ∧ β x ∈ s := by
    filter_upwards [hIo.mem_nhds h0I, hβc.tendsto hsβ] with x hx hxs
    exact ⟨hβder x hx, hxs⟩
  have heq : α =ᶠ[𝓝 (0 : ℝ)] β :=
    ODE_solution_unique_of_eventually (K := K) (s := fun _ ↦ s) (v := fun _ ↦ V)
      (Filter.Eventually.of_forall fun _ ↦ hVs) hαev hβev (hα0.trans hβ0.symm)
  obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.mp heq
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((hUo.inter hIo).mem_nhds ⟨h0U, h0I⟩)
  refine ⟨-ε, ε, by simp [hε], fun x hx ↦ ?_⟩
  have hxb : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hxUI := hball hxb
  calc
    f x = F x := congrArg Prod.fst (hU x hxUI.1)
    _ = (2 : ℝ)^(-1/12 : ℝ) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4))^2)^(1/6 : ℝ) := hformula x hxUI.2
    _ = putnam_2009_a2_solution x := by rfl
