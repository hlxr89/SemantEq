import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_13b_assumed {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).im = c) :
  f a = f b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOn ℂ f s) : (∀ z ∈ s, (f z).im = (f z₀).im) → ∀ z ∈ s, f z = f z₀ := by
  intro him z hz
  let Ω : Set ℂ := {w | w.re < 0} ∪ {w | 0 < w.re}
  let g : ℂ → ℂ := fun w => if w.re < 0 then f z else f z₀
  have hΩ : IsOpen Ω := by
    exact (isOpen_lt Complex.continuous_re continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re)
  have hg : DifferentiableOn ℂ g Ω := by
    intro w hw
    rcases hw with hw | hw
    · change w.re < 0 at hw
      have hn : {w : ℂ | w.re < 0} ∈ 𝓝 w :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hw
      have heq : g =ᶠ[𝓝 w] fun _ => f z := by
        filter_upwards [hn] with y hy
        simp only [g, if_pos hy]
      exact ((differentiableAt_const (𝕜 := ℂ) (f z)).congr_of_eventuallyEq heq).differentiableWithinAt
    · change 0 < w.re at hw
      have hp : {w : ℂ | 0 < w.re} ∈ 𝓝 w :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
      have heq : g =ᶠ[𝓝 w] fun _ => f z₀ := by
        filter_upwards [hp] with y hy
        have hnot : ¬y.re < 0 := not_lt_of_ge (le_of_lt hy)
        simp only [g, if_neg hnot]
      exact ((differentiableAt_const (𝕜 := ℂ) (f z₀)).congr_of_eventuallyEq heq).differentiableWithinAt
  have hgim : ∃ (c : ℝ), ∀ w ∈ Ω, (g w).im = c := by
    refine ⟨(f z₀).im, ?_⟩
    intro w hw
    rcases hw with hw | hw
    · change w.re < 0 at hw
      simp only [g, if_pos hw]
      exact him z hz
    · change 0 < w.re at hw
      have hnot : ¬w.re < 0 := not_lt_of_ge (le_of_lt hw)
      simp only [g, if_neg hnot]
  have hneg : ((-1 : ℂ).re < 0) := neg_one_lt_zero
  have hpos : (0 < (1 : ℂ).re) := zero_lt_one
  have ha : (-1 : ℂ) ∈ Ω := Or.inl hneg
  have hb : (1 : ℂ) ∈ Ω := Or.inr hpos
  have hout := exercise_1_13b_assumed Ω ⟨-1, ha⟩ ⟨1, hb⟩ hΩ hg hgim
  have hnot : ¬((1 : ℂ).re < 0) := not_lt_of_ge zero_le_one
  dsimp only [g] at hout
  rw [if_pos hneg, if_neg hnot] at hout
  exact hout
