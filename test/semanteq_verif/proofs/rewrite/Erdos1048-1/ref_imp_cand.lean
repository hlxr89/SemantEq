import Mathlib

open Polynomial

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos1048

def openLevelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

-- ===== assumed statement (antecedent) =====
theorem erdos_1048_assumed :
    ¬ ∀ (r : ℝ) (f : ℂ[X]), 0 < r → r < 2 → f.Monic → f.degree ≥ 1 → (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
        Metric.ediam (connectedComponentIn (openLevelSet f) z) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_1048_goal :
    ¬ ∀ (r : ℝ) (f : ℂ[X]), r < 2 → f.Monic → f.degree ≥ 1 → (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
        Metric.ediam (connectedComponentIn (openLevelSet f) z) := by
  intro h
  apply erdos_1048_assumed
  intro r f _ hr hM hd hroots
  exact h r f hr hM hd hroots

end Erdos1048
