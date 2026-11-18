import Mathlib

open Topology MvPolynomial Filter Set

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_2009_a2_solution : ℝ → ℝ := fun x ↦ 2 ^ (-(1 : ℝ) / 12) * (Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4)) ^ 2) ^ ((1 : ℝ) / 6)

-- ===== assumed statement (antecedent) =====
theorem putnam_2009_a2_assumed
(f g h : ℝ → ℝ)
(a b : ℝ)
(hab : 0 ∈ Ioo a b)
(hdiff : DifferentiableOn ℝ f (Ioo a b) ∧ DifferentiableOn ℝ g (Ioo a b) ∧ DifferentiableOn ℝ h (Ioo a b))
(hf : (∀ x ∈ Ioo a b, deriv f x = 2 * (f x)^2 * (g x) * (h x) + 1 / ((g x) * (h x))) ∧ f 0 = 1)
(hg : (∀ x ∈ Ioo a b, deriv g x = (f x) * (g x)^2 * (h x) + 4 / ((f x) * (h x))) ∧ g 0 = 1)
(hh : (∀ x ∈ Ioo a b, deriv h x = 3 * (f x) * (g x) * (h x)^2 + 1 / ((f x) * (g x))) ∧ h 0 = 1)
: (∃ c d : ℝ, 0 ∈ Ioo c d ∧ ∀ x ∈ Ioo c d, f x = putnam_2009_a2_solution x) :=
  by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
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
  let V : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦
    (2 * p.1 ^ 2 * p.2.1 * p.2.2 + 1 / (p.2.1 * p.2.2),
      p.1 * p.2.1 ^ 2 * p.2.2 + 4 / (p.1 * p.2.2),
      3 * p.1 * p.2.1 * p.2.2 ^ 2 + 1 / (p.1 * p.2.1))
  have hV : ContDiffAt ℝ 1 V (1, 1, 1) := by
    dsimp [V]
    fun_prop (disch := norm_num)
  obtain ⟨α, hα0, ε, hε, hα⟩ := hV.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have h0mem : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by simp [hε]
  have hc : ContinuousAt α 0 := (hα 0 h0mem).continuousAt
  have hc2 : ContinuousAt (fun x ↦ (α x).2) 0 := hc.snd
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ),
      x ∈ Ioo (0 - ε) (0 + ε) ∧ (α x).1 ≠ 0 ∧ (α x).2.1 ≠ 0 ∧ (α x).2.2 ≠ 0 := by
    filter_upwards [Ioo_mem_nhds (show 0 - ε < (0 : ℝ) by linarith)
        (show (0 : ℝ) < 0 + ε by linarith),
      hc.fst.eventually_ne (y := (0 : ℝ)) (by simp [hα0]),
      hc2.fst.eventually_ne (y := (0 : ℝ)) (by simp [hα0]),
      hc2.snd.eventually_ne (y := (0 : ℝ)) (by simp [hα0])] with x hx h1 h2 h3
    exact ⟨hx, h1, h2, h3⟩
  obtain ⟨I, hI, hopen, h0I⟩ := eventually_nhds_iff.mp hnear
  let f : ℝ → ℝ := fun x ↦ (α x).1
  let g : ℝ → ℝ := fun x ↦ (α x).2.1
  let h : ℝ → ℝ := fun x ↦ (α x).2.2
  have hfder (x : ℝ) (hx : x ∈ I) : HasDerivAt f (V (α x)).1 x := by
    simpa [f] using (hα x (hI x hx).1).hasFDerivAt.fst.hasDerivAt
  have hgder (x : ℝ) (hx : x ∈ I) : HasDerivAt g (V (α x)).2.1 x := by
    simpa [g] using (hα x (hI x hx).1).hasFDerivAt.snd.fst.hasDerivAt
  have hhder (x : ℝ) (hx : x ∈ I) : HasDerivAt h (V (α x)).2.2 x := by
    simpa [h] using (hα x (hI x hx).1).hasFDerivAt.snd.snd.hasDerivAt
  have hsol := putnam_2009_a2_assumed f g h (0 - ε) (0 + ε) h0mem
    ⟨fun x hx ↦ (hα x hx).hasFDerivAt.fst.hasDerivAt.differentiableAt.differentiableWithinAt,
      fun x hx ↦ (hα x hx).hasFDerivAt.snd.fst.hasDerivAt.differentiableAt.differentiableWithinAt,
      fun x hx ↦ (hα x hx).hasFDerivAt.snd.snd.hasDerivAt.differentiableAt.differentiableWithinAt⟩
    ⟨by intro x hx; simpa [f, g, h, V] using (hα x hx).hasFDerivAt.fst.hasDerivAt.deriv,
      by simpa [f, hα0]⟩
    ⟨by intro x hx; simpa [f, g, h, V] using (hα x hx).hasFDerivAt.snd.fst.hasDerivAt.deriv,
      by simpa [g, hα0]⟩
    ⟨by intro x hx; simpa [f, g, h, V] using (hα x hx).hasFDerivAt.snd.snd.hasDerivAt.deriv,
      by simpa [h, hα0]⟩
  obtain ⟨c, d, hcd, heq⟩ := hsol
  let J := I ∩ Ioo c d
  refine ⟨f, g, h, J, hopen.inter isOpen_Ioo, ⟨h0I, hcd⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact (hfder x hx.1).differentiableAt.differentiableWithinAt
  · intro x hx; exact (hgder x hx.1).differentiableAt.differentiableWithinAt
  · intro x hx; exact (hhder x hx.1).differentiableAt.differentiableWithinAt
  · intro x hx; exact ⟨(hI x hx.1).2.1, (hI x hx.1).2.2.1, (hI x hx.1).2.2.2⟩
  · intro x hx; simpa [f, g, h, V] using (hfder x hx.1).deriv
  · intro x hx; simpa [f, g, h, V] using (hgder x hx.1).deriv
  · intro x hx; simpa [f, g, h, V] using (hhder x hx.1).deriv
  · simpa [f, hα0]
  · simpa [g, hα0]
  · simpa [h, hα0]
  · intro x hx
    simpa [putnam_2009_a2_solution] using heq x hx.2
