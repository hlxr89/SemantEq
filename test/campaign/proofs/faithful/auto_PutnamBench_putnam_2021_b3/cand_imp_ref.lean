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
  · intro _ h hh d hd r hr hdr
    have hdx (p : EuclideanSpace ℝ (Fin 2)) :
        deriv (fun x' : ℝ => h !₂[x', p 1]) (p 0) =
          fderiv ℝ h p (EuclideanSpace.single 0 1) := by
      let e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) 0)
      have he : HasFDerivAt (fun x' : ℝ => !₂[x', p 1]) e (p 0) := by
        convert e.hasFDerivAt.add_const (EuclideanSpace.single 1 (p 1)) using 1
        funext x
        ext i
        fin_cases i <;> simp [e]
      have hp : !₂[p 0, p 1] = p := by
        ext i
        fin_cases i <;> simp
      have hh' : HasFDerivAt h (fderiv ℝ h p) p :=
        (hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hh'' : HasFDerivAt h (fderiv ℝ h p) !₂[p 0, p 1] := by
        simpa [hp] using hh'
      have hc : HasFDerivAt (fun x' : ℝ => h !₂[x', p 1])
          ((fderiv ℝ h p).comp e) (p 0) := by
        simpa [Function.comp_def] using hh''.comp (p 0) he
      rw [hc.hasDerivAt.deriv]
      change (fderiv ℝ h p) (e 1) = _
      congr 1
    have hdy (p : EuclideanSpace ℝ (Fin 2)) :
        deriv (fun y' : ℝ => h !₂[p 0, y']) (p 1) =
          fderiv ℝ h p (EuclideanSpace.single 1 1) := by
      let e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) 1)
      have he : HasFDerivAt (fun y' : ℝ => !₂[p 0, y']) e (p 1) := by
        convert e.hasFDerivAt.add_const (EuclideanSpace.single 0 (p 0)) using 1
        funext y
        ext i
        fin_cases i <;> simp [e]
      have hp : !₂[p 0, p 1] = p := by
        ext i
        fin_cases i <;> simp
      have hh' : HasFDerivAt h (fderiv ℝ h p) p :=
        (hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hh'' : HasFDerivAt h (fderiv ℝ h p) !₂[p 0, p 1] := by
        simpa [hp] using hh'
      have hc : HasFDerivAt (fun y' : ℝ => h !₂[p 0, y'])
          ((fderiv ℝ h p).comp e) (p 1) := by
        simpa [Function.comp_def] using hh''.comp (p 1) he
      rw [hc.hasDerivAt.deriv]
      change (fderiv ℝ h p) (e 1) = _
      congr 1
    let ρ : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
      p 1 * fderiv ℝ h p (EuclideanSpace.single 0 1) -
        p 0 * fderiv ℝ h p (EuclideanSpace.single 1 1)
    obtain ⟨c, hc, hint⟩ := putnam_2021_b3_assumed h hh ρ (by intros; rfl) d r hr hdr
    refine ⟨c, hc, ?_⟩
    have hfun : rho h = ρ := by
      funext p
      rw [rho_def, hdx p, hdy p]
    simpa only [hfun] using hint
