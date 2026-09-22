import Mathlib

open Filter Topology Metric MeasureTheory

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2021_b3_solution : Prop := True

-- ===== assumed statement (antecedent) =====
theorem putnam_2021_b3_refs_assumed
  (rho : ((EuclideanSpace ℝ (Fin 2)) → ℝ) → (EuclideanSpace ℝ (Fin 2)) → ℝ)
  (rho_def : ∀ (h : (EuclideanSpace ℝ (Fin 2)) → ℝ) (p : EuclideanSpace ℝ (Fin 2)),
    rho h p = (p 1) *
      deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0)
      - (p 0) * deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1)) :
  (∀ h : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiff ℝ 2 h →
    (∀ d > 0, ∀ r > 0, d > r → (∃ c : EuclideanSpace ℝ (Fin 2), dist c 0 = d ∧ (∫ p in (ball c r), rho h p) = 0)))
  ↔ putnam_2021_b3_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2021_b3 (h : EuclideanSpace ℝ (Fin 2) → ℝ) (hh : ContDiff ℝ 2 h)
    (ρ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hρ : ∀ p, ρ p = p 1 * fderiv ℝ h p (EuclideanSpace.single 0 1) -
      p 0 * fderiv ℝ h p (EuclideanSpace.single 1 1))
    (d r : ℝ) (hr : 0 < r) (hdr : r < d) :
    ∃ c : EuclideanSpace ℝ (Fin 2), dist c 0 = d ∧
      ∫ p in Metric.ball c r, ρ p = 0 := by
  let rho' : ((EuclideanSpace ℝ (Fin 2)) → ℝ) →
      (EuclideanSpace ℝ (Fin 2)) → ℝ := fun g p =>
    (p 1) * deriv (fun x' : ℝ => g !₂[x', p 1]) (p 0) -
      (p 0) * deriv (fun y' : ℝ => g !₂[p 0, y']) (p 1)
  have hall := (putnam_2021_b3_refs_assumed rho' (by
    intro g p
    rfl)).mpr trivial
  obtain ⟨c, hc, hInt⟩ := hall h hh d (lt_trans hr hdr) r hr hdr
  have hx : ∀ p : EuclideanSpace ℝ (Fin 2),
      deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0) =
        fderiv ℝ h p (EuclideanSpace.single 0 1) := by
    intro p
    apply HasDerivAt.deriv
    have hline : HasDerivAt
        (fun x : ℝ => p + (x - p 0) • EuclideanSpace.single 0 1)
        (EuclideanSpace.single 0 1) (p 0) := by
      convert (hasDerivAt_const (x := p 0) p).add
        (((hasDerivAt_id (x := p 0)).sub_const (p 0)).smul_const
          (EuclideanSpace.single 0 1)) using 1 <;> simp
    have hvec : HasDerivAt (fun x : ℝ => !₂[x, p 1])
        (EuclideanSpace.single 0 1) (p 0) := by
      have hfun : (fun x : ℝ => !₂[x, p 1]) =
          (fun x : ℝ => p + (x - p 0) • EuclideanSpace.single 0 1) := by
        funext x
        ext j
        fin_cases j <;> simp
      rw [hfun]
      exact hline
    have hp : !₂[p 0, p 1] = p := by
      ext j
      fin_cases j <;> simp
    have hout : HasFDerivAt h (fderiv ℝ h p) !₂[p 0, p 1] := by
      simpa [hp] using (hh.differentiable (by norm_num) p).hasFDerivAt
    simpa [Function.comp_def] using hout.comp_hasDerivAt _ hvec
  have hy : ∀ p : EuclideanSpace ℝ (Fin 2),
      deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1) =
        fderiv ℝ h p (EuclideanSpace.single 1 1) := by
    intro p
    apply HasDerivAt.deriv
    have hline : HasDerivAt
        (fun y : ℝ => p + (y - p 1) • EuclideanSpace.single 1 1)
        (EuclideanSpace.single 1 1) (p 1) := by
      convert (hasDerivAt_const (x := p 1) p).add
        (((hasDerivAt_id (x := p 1)).sub_const (p 1)).smul_const
          (EuclideanSpace.single 1 1)) using 1 <;> simp
    have hvec : HasDerivAt (fun y : ℝ => !₂[p 0, y])
        (EuclideanSpace.single 1 1) (p 1) := by
      have hfun : (fun y : ℝ => !₂[p 0, y]) =
          (fun y : ℝ => p + (y - p 1) • EuclideanSpace.single 1 1) := by
        funext y
        ext j
        fin_cases j <;> simp
      rw [hfun]
      exact hline
    have hp : !₂[p 0, p 1] = p := by
      ext j
      fin_cases j <;> simp
    have hout : HasFDerivAt h (fderiv ℝ h p) !₂[p 0, p 1] := by
      simpa [hp] using (hh.differentiable (by norm_num) p).hasFDerivAt
    simpa [Function.comp_def] using hout.comp_hasDerivAt _ hvec
  have heq : ρ = rho' h := by
    funext p
    rw [hρ p]
    change p 1 * fderiv ℝ h p (EuclideanSpace.single 0 1) -
      p 0 * fderiv ℝ h p (EuclideanSpace.single 1 1) =
      p 1 * deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0) -
        p 0 * deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1)
    rw [hx p, hy p]
  refine ⟨c, hc, ?_⟩
  rw [heq]
  exact hInt
