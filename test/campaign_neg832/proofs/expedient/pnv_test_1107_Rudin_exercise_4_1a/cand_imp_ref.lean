import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ (x : ℝ), Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : Tendsto f (𝓝 0) (𝓝 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  let f : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst x
      simpa [f] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
    · have hevent : ∀ᶠ y in 𝓝 (0 : ℝ), f (x + y) - f (x - y) = 0 := by
        filter_upwards [eventually_ne_nhds (show (0 : ℝ) ≠ -x by simpa using hx),
          eventually_ne_nhds (show (0 : ℝ) ≠ x by exact Ne.symm hx)] with y hy hxy
        have hp : x + y ≠ 0 := by intro h; apply hy; linarith
        have hm : x - y ≠ 0 := by intro h; apply hxy; linarith
        simp [f, hp, hm]
      rw [tendsto_congr' hevent]
      exact tendsto_const_nhds
  · intro h
    have hopen : IsOpen (f ⁻¹' Set.Ioi (1 / 2 : ℝ)) := isOpen_Ioi.preimage h
    have heq : f ⁻¹' Set.Ioi (1 / 2 : ℝ) = {0} := by
      ext x
      by_cases hx : x = 0 <;> norm_num [f, hx]
    rw [heq] at hopen
    exact not_isOpen_singleton 0 hopen
