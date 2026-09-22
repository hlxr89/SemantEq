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
    let g : ℝ+ → ℝ+ := fun x ↦ ⟨f x, hpos x x.property⟩
    have hgfun : ∀ x y, g (x * g y) = y * g x := by
      intro x y
      apply Subtype.ext
      exact hfun x y x.property y.property
    have hgbound : ∀ ε, ∃ x, ∀ y, x < y → g y < ε := by
      intro ε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop'.mp hlim) ε ε.property
      let x : ℝ+ := ⟨max 1 (N + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _)⟩
      refine ⟨x, fun y hxy ↦ ?_⟩
      have hyN : N < (y : ℝ) := lt_trans (lt_add_one N) (lt_of_le_of_lt (le_max_right _ _) hxy)
      have := hN y hyN
      simpa [g, Real.dist_eq, abs_of_pos (hpos y y.property)] using this
    have hg := (Imo1983P1_refs_assumed g).2 ⟨hgfun, hgbound⟩
    intro x hx
    have := congrArg Subtype.val (congrFun hg ⟨x, hx⟩)
    simpa [SolutionSet, g] using this
  · intro hf
    have hf' : ∀ x : ℝ, 0 < x → f x = 1 / x := hf
    constructor
    · intro x hx
      rw [hf' x hx]
      positivity
    constructor
    · intro x y hx hy
      rw [hf' y hy, hf' x hx]
      rw [hf' (x * (1 / y)) (by positivity)]
      field_simp
    · apply tendsto_inv_atTop_zero.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simpa [one_div] using (hf' x hx).symm
