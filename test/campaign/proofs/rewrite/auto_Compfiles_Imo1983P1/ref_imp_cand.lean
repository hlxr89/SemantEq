import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

def SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

/-- The functions solving the problem: `f x = 1 / x` (on the positive reals). -/
def Imo1983P1_solution : Set (ℝ → ℝ) := {f | ∀ x : ℝ, 0 < x → f x = 1 / x}

-- ===== assumed statement (antecedent) =====
theorem Imo1983P1_refs_assumed (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo1983P1 (f : ℝ → ℝ) :
    ((∀ x : ℝ, 0 < x → 0 < f x) ∧
      (∀ x y : ℝ, 0 < x → 0 < y → f (x * f y) = y * f x) ∧
      Tendsto f atTop (nhds 0)) ↔
    f ∈ Imo1983P1_solution := by
  constructor
  · rintro ⟨hpos, hfun, hlim⟩
    let g : ℝ+ → ℝ+ := fun z ↦ ⟨f z, hpos z z.property⟩
    have hgfun : ∀ x y, g (x * g y) = y * g x := by
      intro x y
      apply Subtype.ext
      exact hfun x y x.property y.property
    have hgeps : ∀ ε : ℝ+, ∃ x : ℝ+, ∀ y, x < y → g y < ε := by
      intro ε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε ε.property
      let x : ℝ+ := ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1)⟩
      refine ⟨x, ?_⟩
      intro y hxy
      have hNy : N ≤ (y : ℝ) := le_trans (le_max_left N 1) (le_of_lt hxy)
      have hydist := hN y hNy
      simpa only [g, Real.dist_eq, sub_zero, abs_of_pos (hpos y y.property)] using hydist
    have hgmem := (Imo1983P1_refs_assumed g).2 ⟨hgfun, hgeps⟩
    change ∀ x : ℝ, 0 < x → f x = 1 / x
    intro x hx
    change g = (fun z : ℝ+ ↦ 1 / z) at hgmem
    have hv := congrArg Subtype.val (congrFun hgmem (⟨x, hx⟩ : ℝ+))
    exact hv
  · intro hsol
    change ∀ x : ℝ, 0 < x → f x = 1 / x at hsol
    have hpos : ∀ x : ℝ, 0 < x → 0 < f x := by
      intro x hx
      rw [hsol x hx]
      exact one_div_pos.mpr hx
    let g : ℝ+ → ℝ+ := fun z ↦ ⟨f z, hpos z z.property⟩
    have hgmem : g ∈ SolutionSet := by
      change g = fun z : ℝ+ ↦ 1 / z
      funext z
      apply Subtype.ext
      exact hsol z z.property
    obtain ⟨hgfun, hgeps⟩ := (Imo1983P1_refs_assumed g).1 hgmem
    refine ⟨hpos, ?_, ?_⟩
    · intro x y hx hy
      have hv := congrArg Subtype.val (hgfun (⟨x, hx⟩ : ℝ+) (⟨y, hy⟩ : ℝ+))
      exact hv
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨X, hX⟩ := hgeps (⟨ε, hε⟩ : ℝ+)
      refine ⟨(X : ℝ) + 1, ?_⟩
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le (lt_trans X.property (lt_add_one (X : ℝ))) hn
      have hXn_real : (X : ℝ) < n := lt_of_lt_of_le (lt_add_one (X : ℝ)) hn
      have hXn : X < (⟨n, hnpos⟩ : ℝ+) := hXn_real
      have hv := hX (⟨n, hnpos⟩ : ℝ+) hXn
      simpa only [g, Real.dist_eq, sub_zero, abs_of_pos (hpos n hnpos)] using hv
