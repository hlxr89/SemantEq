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
    (2 * p.1^2 * p.2.1 * p.2.2 + 1 / (p.2.1 * p.2.2),
      p.1 * p.2.1^2 * p.2.2 + 4 / (p.1 * p.2.2),
      3 * p.1 * p.2.1 * p.2.2^2 + 1 / (p.1 * p.2.1))
  have hV : ContDiffAt ℝ 1 V (1, 1, 1) := by
    dsimp [V]
    fun_prop (disch := norm_num)
  obtain ⟨A, hA0, ε, hε0, hsol⟩ :=
    hV.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  have hmem : ((1 : ℝ), (1 : ℝ), (1 : ℝ)) ∈
      Metric.closedBall ((1 : ℝ), (1 : ℝ), (1 : ℝ)) A :=
    Metric.mem_closedBall_self (le_of_lt hA0)
  specialize hsol (1, 1, 1) hmem
  obtain ⟨α, hα0, hα⟩ := hsol
  let f : ℝ → ℝ := fun x ↦ (α x).1
  let g : ℝ → ℝ := fun x ↦ (α x).2.1
  let h : ℝ → ℝ := fun x ↦ (α x).2.2
  let I : Set ℝ := Ioo (-ε) ε
  have hfd (x : ℝ) (hx : x ∈ I) : HasDerivAt f (V (α x)).1 x :=
    (hα x (by simpa [I] using hx)).fst
  have hgd (x : ℝ) (hx : x ∈ I) : HasDerivAt g (V (α x)).2.1 x :=
    (hα x (by simpa [I] using hx)).snd.fst
  have hhd (x : ℝ) (hx : x ∈ I) : HasDerivAt h (V (α x)).2.2 x :=
    (hα x (by simpa [I] using hx)).snd.snd
  have hf0 : f 0 = 1 := by simp [f, hα0]
  have hg0 : g 0 = 1 := by simp [g, hα0]
  have hh0 : h 0 = 1 := by simp [h, hα0]
  obtain ⟨c, d, hcd, hformula⟩ := putnam_2009_a2_assumed f g h (-ε) ε
    (by simp [hε0])
    ⟨fun x hx ↦ (hfd x hx).differentiableAt.differentiableWithinAt,
      fun x hx ↦ (hgd x hx).differentiableAt.differentiableWithinAt,
      fun x hx ↦ (hhd x hx).differentiableAt.differentiableWithinAt⟩
    ⟨fun x hx ↦ by simpa [f, g, h, V] using (hfd x hx).deriv, hf0⟩
    ⟨fun x hx ↦ by simpa [f, g, h, V] using (hgd x hx).deriv, hg0⟩
    ⟨fun x hx ↦ by simpa [f, g, h, V] using (hhd x hx).deriv, hh0⟩
  refine ⟨I, f, g, h, isOpen_Ioo, by simp [I, hε0], ?_, ?_, ?_, ?_, ?_, ?_,
    hf0, hg0, hh0, Ioo c d ∩ I, isOpen_Ioo.inter isOpen_Ioo, ⟨hcd, by simp [I, hε0]⟩,
    inter_subset_right, ?_⟩
  · exact fun x hx ↦ (hfd x hx).differentiableAt.differentiableWithinAt
  · exact fun x hx ↦ (hgd x hx).differentiableAt.differentiableWithinAt
  · exact fun x hx ↦ (hhd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    simpa [f, g, h, V] using (hfd x hx).deriv
  · intro x hx
    simpa [f, g, h, V] using (hgd x hx).deriv
  · intro x hx
    simpa [f, g, h, V] using (hhd x hx).deriv
  · intro x hx
    simpa [putnam_2009_a2_solution] using hformula x hx.1
