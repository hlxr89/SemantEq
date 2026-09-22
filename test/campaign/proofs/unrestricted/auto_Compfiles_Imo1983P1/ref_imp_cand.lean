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
    let g : ℝ+ → ℝ+ := fun x => ⟨f x, hpos x x.property⟩
    have hgfun : ∀ x y, g (x * g y) = y * g x := by
      intro x y
      apply Subtype.ext
      exact hfun x y x.property y.property
    have hgeps : ∀ ε, ∃ x, ∀ y, x < y → g y < ε := by
      intro ε
      have hev : ∀ᶠ y : ℝ in atTop, f y < ε :=
        hlim.eventually (Iio_mem_nhds ε.property)
      rcases (eventually_atTop.1 hev) with ⟨a, ha⟩
      let x : ℝ+ := ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩
      refine ⟨x, ?_⟩
      intro y hy
      exact ha y (le_trans (le_max_left _ _) (le_of_lt hy))
    have hg : g ∈ SolutionSet :=
      (Imo1983P1_refs_assumed g).2 ⟨hgfun, hgeps⟩
    intro x hx
    have heq : g = fun z => 1 / z := hg
    have := congrFun heq (⟨x, hx⟩ : ℝ+)
    exact congrArg Subtype.val this
  · intro hf
    have hformula : ∀ x : ℝ, 0 < x → f x = 1 / x := hf
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [hformula x hx]
      positivity
    · intro x y hx hy
      have hfy : f y = 1 / y := hformula y hy
      have hxy : 0 < x * f y := mul_pos hx (by rw [hfy]; positivity)
      calc
        f (x * f y) = 1 / (x * f y) := hformula _ hxy
        _ = y * (1 / x) := by rw [hfy]; field_simp
        _ = y * f x := by rw [hformula x hx]
    · have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
        simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
      apply Filter.Tendsto.congr' _ hinv
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (hformula x hx).symm
