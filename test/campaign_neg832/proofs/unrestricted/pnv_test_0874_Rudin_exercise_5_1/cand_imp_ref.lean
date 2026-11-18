import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) {s : Set ℝ} (hs : s.Countable) (hf : DifferentiableOn ℝ f s) (hf' : ∀ x ∈ s, DifferentiableAt ℝ f x) (hfd : ∀ x ∈ s, DifferentiableWithinAt ℝ (fderiv ℝ f x) s x) : ∃ C : ℝ, ∀ x ∈ s, ‖fderivWithin ℝ f s x‖ ≤ C := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, |(f x - f y)| ≤ (x - y) ^ 2) :
  ∃ c, f = λ x => c := by
  exfalso
  let s : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  have hs : s.Countable := Set.countable_range _
  have hsq : DifferentiableOn ℝ (fun x : ℝ => x ^ 2) s := by
    intro x hx
    exact (differentiableAt_pow 2).differentiableWithinAt
  have hsq' : ∀ x ∈ s, DifferentiableAt ℝ (fun x : ℝ => x ^ 2) x := by
    intro x hx
    exact differentiableAt_pow 2
  have hsqd : ∀ x ∈ s, DifferentiableWithinAt ℝ
      (fderiv ℝ (fun x : ℝ => x ^ 2) x) s x := by
    intro x hx
    fun_prop
  obtain ⟨C, hC⟩ := dummy_assumed (fun x : ℝ => x ^ 2) hs hsq hsq' hsqd
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (|C| / 2)
  let x : ℝ := n
  have hxs : x ∈ s := ⟨(n : ℚ), by simp [x]⟩
  have hud : UniqueDiffWithinAt ℝ s x := by
    apply (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := x)).mono_closure
    rw [Rat.denseRange_cast.closure_range]
  have hfw : fderivWithin ℝ (fun x : ℝ => x ^ 2) s x =
      ContinuousLinearMap.toSpanSingleton ℝ (2 * x) := by
    simpa using (hasDerivAt_pow 2 x).hasFDerivAt.hasFDerivWithinAt.fderivWithin hud
  have hb := hC x hxs
  rw [hfw] at hb
  have hnorm : ‖ContinuousLinearMap.toSpanSingleton ℝ (2 * x)‖ = |2 * x| := by
    simp
  rw [hnorm] at hb
  have hCx : C < 2 * x := by
    have habs : |C| < 2 * x := by
      dsimp [x]
      nlinarith [hn]
    exact lt_of_le_of_lt (le_abs_self C) habs
  have hnonneg : 0 ≤ 2 * x := by positivity
  rw [abs_of_nonneg hnonneg] at hb
  exact (not_lt_of_ge hb) hCx
