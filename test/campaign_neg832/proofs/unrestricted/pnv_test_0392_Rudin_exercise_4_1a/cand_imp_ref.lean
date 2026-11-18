import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ (x : ℝ), ∃ (h : ℝ), ∀ (h0 : 0 < h), |f (x + h) - f x| < h) (h : ¬ UniformContinuous f) : ∃ x : ℝ, ContinuousAt f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  let f : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst x
      simp [f]
    · have hp : Tendsto (fun y : ℝ => x + y) (𝓝 0) (𝓝 x) := by
        convert (tendsto_const_nhds (x := x)).add
          (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 0) (𝓝 0)) using 1 <;> simp
      have hm : Tendsto (fun y : ℝ => x - y) (𝓝 0) (𝓝 x) := by
        convert (tendsto_const_nhds (x := x)).sub
          (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 0) (𝓝 0)) using 1 <;> simp
      refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0)).congr' ?_
      filter_upwards [hp.eventually (eventually_ne_nhds hx),
        hm.eventually (eventually_ne_nhds hx)] with y hyp hym
      simp [f, hyp, hym]
  · intro hcont
    have hopen : IsOpen (f ⁻¹' Set.Ioi (0 : ℝ)) := isOpen_Ioi.preimage hcont
    have heq : f ⁻¹' Set.Ioi (0 : ℝ) = ({0} : Set ℝ) := by
      ext x
      by_cases hx : x = 0
      · simp [f, hx]
      · simp [f, hx]
    rw [heq] at hopen
    exact not_isOpen_singleton 0 hopen
