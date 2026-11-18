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
  obtain ⟨I, F, G, H, hI, h0I, hFd, hGd, hHd, hFeq, hGeq, hHeq,
    hF0, hG0, hH0, J, hJ, h0J, hJI, hsol⟩ := problem_statement_assumed
  let V : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p ↦
    (2 * p.1 ^ 2 * p.2.1 * p.2.2 + 1 / (p.2.1 * p.2.2),
      p.1 * p.2.1 ^ 2 * p.2.2 + 4 / (p.1 * p.2.2),
      3 * p.1 * p.2.1 * p.2.2 ^ 2 + 1 / (p.1 * p.2.1))
  have hV : ContDiffAt ℝ 1 V (1, 1, 1) := by
    dsimp [V]
    fun_prop (disch := norm_num)
  let α : ℝ → ℝ × ℝ × ℝ := fun x ↦ (f x, g x, h x)
  let β : ℝ → ℝ × ℝ × ℝ := fun x ↦ (F x, G x, H x)
  have hαder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt α (V (α x)) x := by
    have hdf := (hdiff.1.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have hdg := (hdiff.2.1.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have hdh := (hdiff.2.2.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    simpa [α, V, hf.1 x hx, hg.1 x hx, hh.1 x hx] using hdf.prodMk (hdg.prodMk hdh)
  have hβder (x : ℝ) (hx : x ∈ I) : HasDerivAt β (V (β x)) x := by
    have hdF := (hFd.differentiableAt (hI.mem_nhds hx)).hasDerivAt
    have hdG := (hGd.differentiableAt (hI.mem_nhds hx)).hasDerivAt
    have hdH := (hHd.differentiableAt (hI.mem_nhds hx)).hasDerivAt
    simpa [β, V, hFeq x hx, hGeq x hx, hHeq x hx] using hdF.prodMk (hdG.prodMk hdH)
  have hα0 : α 0 = (1, 1, 1) := by simp [α, hf.2, hg.2, hh.2]
  have hβ0 : β 0 = (1, 1, 1) := by simp [β, hF0, hG0, hH0]
  obtain ⟨K, s, hs, hLip⟩ := hV.exists_lipschitzOnWith
  have hαs : ∀ᶠ x in 𝓝 0, α x ∈ s := by
    apply (hαder 0 hab).continuousAt
    simpa [hα0] using hs
  have hβs : ∀ᶠ x in 𝓝 0, β x ∈ s := by
    apply (hβder 0 h0I).continuousAt
    simpa [hβ0] using hs
  have hαode : ∀ᶠ x in 𝓝 0, HasDerivAt α (V (α x)) x ∧ α x ∈ s := by
    filter_upwards [isOpen_Ioo.mem_nhds hab, hαs] with x hx hxs
    exact ⟨hαder x hx, hxs⟩
  have hβode : ∀ᶠ x in 𝓝 0, HasDerivAt β (V (β x)) x ∧ β x ∈ s := by
    filter_upwards [hI.mem_nhds h0I, hβs] with x hx hxs
    exact ⟨hβder x hx, hxs⟩
  have hαβ : α =ᶠ[𝓝 0] β :=
    ODE_solution_unique_of_eventually (v := fun _ ↦ V) (s := fun _ ↦ s)
      (Filter.Eventually.of_forall fun _ ↦ hLip) hαode hβode (hα0.trans hβ0.symm)
  have hall : ∀ᶠ x in 𝓝 0, α x = β x ∧ x ∈ J := hαβ.and (hJ.mem_nhds h0J)
  obtain ⟨c, d, hcd, hsub⟩ := hall.exists_Ioo_subset
  refine ⟨c, d, hcd, ?_⟩
  intro x hx
  have hx' := hsub hx
  calc
    f x = F x := by simpa [α, β] using congrArg Prod.fst hx'.1
    _ = putnam_2009_a2_solution x := by
      simpa [putnam_2009_a2_solution] using hsol x hx'.2
