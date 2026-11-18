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
: (∃ c d : ℝ, 0 ∈ Ioo c d ∧ ∀ x ∈ Ioo c d, f x = putnam_2009_a2_solution x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∃ (I : Set ℝ) (f g h : ℝ → ℝ),
    IsOpen I ∧ 0 ∈ I ∧
    DifferentiableOn ℝ f I ∧ DifferentiableOn ℝ g I ∧ DifferentiableOn ℝ h I ∧
    (∀ x ∈ I, deriv f x = 2 * (f x)^2 * g x * h x + 1 / (g x * h x)) ∧
    (∀ x ∈ I, deriv g x = f x * (g x)^2 * h x + 4 / (f x * h x)) ∧
    (∀ x ∈ I, deriv h x = 3 * f x * g x * (h x)^2 + 1 / (f x * g x)) ∧
    f 0 = 1 ∧ g 0 = 1 ∧ h 0 = 1 ∧
    (∃ (J : Set ℝ), IsOpen J ∧ 0 ∈ J ∧ J ⊆ I ∧
      ∀ x ∈ J, f x = (2 : ℝ)^(-(1:ℝ)/12) * ((Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4))^2))^(1/6 : ℝ)) := by
  let V : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦
    (2 * p.1 ^ 2 * p.2.1 * p.2.2 + 1 / (p.2.1 * p.2.2),
      p.1 * p.2.1 ^ 2 * p.2.2 + 4 / (p.1 * p.2.2),
      3 * p.1 * p.2.1 * p.2.2 ^ 2 + 1 / (p.1 * p.2.1))
  have hV : ContDiffAt ℝ 1 V (1, 1, 1) := by
    dsimp [V]
    fun_prop (disch := norm_num)
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hV.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  let f : ℝ → ℝ := fun x ↦ (α x).1
  let g : ℝ → ℝ := fun x ↦ (α x).2.1
  let h : ℝ → ℝ := fun x ↦ (α x).2.2
  have hder_f (x : ℝ) (hx : x ∈ Ioo (0 - ε) (0 + ε)) :
      HasDerivAt f (V (α x)).1 x := by
    simpa [f] using (hα x hx).hasFDerivAt.fst.hasDerivAt
  have hder_g (x : ℝ) (hx : x ∈ Ioo (0 - ε) (0 + ε)) :
      HasDerivAt g (V (α x)).2.1 x := by
    simpa [g] using (hα x hx).hasFDerivAt.snd.fst.hasDerivAt
  have hder_h (x : ℝ) (hx : x ∈ Ioo (0 - ε) (0 + ε)) :
      HasDerivAt h (V (α x)).2.2 x := by
    simpa [h] using (hα x hx).hasFDerivAt.snd.snd.hasDerivAt
  have hab : 0 ∈ Ioo (0 - ε) (0 + ε) := by simp [hε]
  have hf0 : f 0 = 1 := by simpa [f] using congrArg Prod.fst hα0
  have hg0 : g 0 = 1 := by simpa [g] using congrArg (fun p ↦ p.2.1) hα0
  have hh0 : h 0 = 1 := by simpa [h] using congrArg (fun p ↦ p.2.2) hα0
  have Hf : ∀ x ∈ Ioo (0 - ε) (0 + ε),
      deriv f x = 2 * (f x)^2 * g x * h x + 1 / (g x * h x) := by
    intro x hx
    simpa [V, f, g, h] using (hder_f x hx).deriv
  have Hg : ∀ x ∈ Ioo (0 - ε) (0 + ε),
      deriv g x = f x * (g x)^2 * h x + 4 / (f x * h x) := by
    intro x hx
    simpa [V, f, g, h] using (hder_g x hx).deriv
  have Hh : ∀ x ∈ Ioo (0 - ε) (0 + ε),
      deriv h x = 3 * f x * g x * (h x)^2 + 1 / (f x * g x) := by
    intro x hx
    simpa [V, f, g, h] using (hder_h x hx).deriv
  obtain ⟨c, d, hcd, Hsol⟩ := putnam_2009_a2_assumed f g h (0 - ε) (0 + ε) hab
    ⟨fun x hx ↦ (hder_f x hx).differentiableAt.differentiableWithinAt,
      fun x hx ↦ (hder_g x hx).differentiableAt.differentiableWithinAt,
      fun x hx ↦ (hder_h x hx).differentiableAt.differentiableWithinAt⟩
    ⟨Hf, hf0⟩ ⟨Hg, hg0⟩ ⟨Hh, hh0⟩
  refine ⟨Ioo (0 - ε) (0 + ε), f, g, h, isOpen_Ioo, hab,
    fun x hx ↦ (hder_f x hx).differentiableAt.differentiableWithinAt,
    fun x hx ↦ (hder_g x hx).differentiableAt.differentiableWithinAt,
    fun x hx ↦ (hder_h x hx).differentiableAt.differentiableWithinAt,
    Hf, Hg, Hh, hf0, hg0, hh0, Ioo c d ∩ Ioo (0 - ε) (0 + ε),
    isOpen_Ioo.inter isOpen_Ioo, ⟨hcd, hab⟩, inter_subset_right, ?_⟩
  intro x hx
  simpa [putnam_2009_a2_solution] using Hsol x hx.1
