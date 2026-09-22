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
    have hx : ∀ p : EuclideanSpace ℝ (Fin 2),
        deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0) =
          fderiv ℝ h p (EuclideanSpace.single 0 1) := by
      intro p
      have hp : !₂[p 0, p 1] = p := by
        ext i
        fin_cases i <;> rfl
      have hcurve : HasDerivAt (fun x' : ℝ => !₂[x', p 1])
          (EuclideanSpace.single 0 1) (p 0) := by
        let v0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
        let v1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (p 1)
        have heq : (fun x' : ℝ => !₂[x', p 1]) = (fun x => x • v0 + v1) := by
          funext x
          apply WithLp.ofLp_injective
          funext i
          fin_cases i <;> simp [v0, v1, EuclideanSpace.single_apply]
        rw [heq]
        simpa only [id_eq, one_smul, v0] using
          ((hasDerivAt_id (x := p 0)).smul_const v0).add_const v1
      have hc := (hh.differentiable two_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt
        (p 0) hcurve
      rw [hp] at hc
      exact hc.deriv
    have hy : ∀ p : EuclideanSpace ℝ (Fin 2),
        deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1) =
          fderiv ℝ h p (EuclideanSpace.single 1 1) := by
      intro p
      have hp : !₂[p 0, p 1] = p := by
        ext i
        fin_cases i <;> rfl
      have hcurve : HasDerivAt (fun y' : ℝ => !₂[p 0, y'])
          (EuclideanSpace.single 1 1) (p 1) := by
        let v0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (p 0)
        let v1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
        have heq : (fun y' : ℝ => !₂[p 0, y']) = (fun y => v0 + y • v1) := by
          funext y
          apply WithLp.ofLp_injective
          funext i
          fin_cases i <;> simp [v0, v1, EuclideanSpace.single_apply]
        rw [heq]
        simpa only [id_eq, one_smul, v1] using
          ((hasDerivAt_id (x := p 1)).smul_const v1).const_add v0
      have hc := (hh.differentiable two_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt
        (p 1) hcurve
      rw [hp] at hc
      exact hc.deriv
    apply putnam_2021_b3_assumed h hh (rho h)
    · intro p
      rw [rho_def h p, hx p, hy p]
    · exact hr
    · exact hdr
