import Mathlib

open Filter Topology Metric
open MeasureTheory

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_2021_b3_solution : Prop := True

-- ===== assumed statement (antecedent) =====
theorem putnam_2021_b3_assumed (h : EuclideanSpace ℝ (Fin 2) → ℝ) (hh : ContDiff ℝ 2 h)
    (ρ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hρ : ∀ p, ρ p = p 1 * fderiv ℝ h p (EuclideanSpace.single 0 1) -
      p 0 * fderiv ℝ h p (EuclideanSpace.single 1 1))
    (d r : ℝ) (hr : 0 < r) (hdr : r < d) :
    ∃ c : EuclideanSpace ℝ (Fin 2), dist c 0 = d ∧
      ∫ p in Metric.ball c r, ρ p = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2021_b3_refs
  (rho : ((EuclideanSpace ℝ (Fin 2)) → ℝ) → (EuclideanSpace ℝ (Fin 2)) → ℝ)
  (rho_def : ∀ (h : (EuclideanSpace ℝ (Fin 2)) → ℝ) (p : EuclideanSpace ℝ (Fin 2)),
    rho h p = (p 1) *
      deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0)
      - (p 0) * deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1)) :
  (∀ h : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiff ℝ 2 h →
    (∀ d > 0, ∀ r > 0, d > r → (∃ c : EuclideanSpace ℝ (Fin 2), dist c 0 = d ∧ (∫ p in (ball c r), rho h p) = 0)))
  ↔ putnam_2021_b3_solution := by
  constructor
  · intro _
    trivial
  · intro _ h hh d _ r hr hdr
    have deriv_zero (p : EuclideanSpace ℝ (Fin 2)) :
        deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0) =
          fderiv ℝ h p (EuclideanSpace.single 0 1) := by
      let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) 0)
      let q : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (p 1)
      have hc : HasFDerivAt (fun x : ℝ => L x + q) L (p 0) := L.hasFDerivAt.add_const q
      have hcurve : (fun x : ℝ => L x + q) = (fun x' : ℝ => !₂[x', p 1]) := by
        funext x
        ext i
        fin_cases i <;> simp [L, q]
      rw [hcurve] at hc
      have hp : !₂[p 0, p 1] = p := by ext i; fin_cases i <;> simp
      have hL : L 1 = EuclideanSpace.single 0 1 := by
        ext i
        fin_cases i <;> simp [L]
      have hd := (hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp
        (p 0) hc
      rw [hp] at hd
      simpa [Function.comp_def, hL] using hd.hasDerivAt.deriv
    have deriv_one (p : EuclideanSpace ℝ (Fin 2)) :
        deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1) =
          fderiv ℝ h p (EuclideanSpace.single 1 1) := by
      let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) 1)
      let q : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (p 0)
      have hc : HasFDerivAt (fun y : ℝ => L y + q) L (p 1) := L.hasFDerivAt.add_const q
      have hcurve : (fun y : ℝ => L y + q) = (fun y' : ℝ => !₂[p 0, y']) := by
        funext y
        ext i
        fin_cases i <;> simp [L, q]
      rw [hcurve] at hc
      have hp : !₂[p 0, p 1] = p := by ext i; fin_cases i <;> simp
      have hL : L 1 = EuclideanSpace.single 1 1 := by
        ext i
        fin_cases i <;> simp [L]
      have hd := (hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp
        (p 1) hc
      rw [hp] at hd
      simpa [Function.comp_def, hL] using hd.hasDerivAt.deriv
    apply putnam_2021_b3_assumed h hh (rho h) _ d r hr hdr
    intro p
    rw [rho_def, deriv_zero, deriv_one]
