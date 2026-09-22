import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

def SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

/-- The functions solving the problem: `f x = 1 / x` (on the positive reals). -/
def Imo1983P1_solution : Set (ℝ → ℝ) := {f | ∀ x : ℝ, 0 < x → f x = 1 / x}

-- ===== assumed statement (antecedent) =====
theorem Imo1983P1_assumed (f : ℝ → ℝ) :
    ((∀ x : ℝ, 0 < x → 0 < f x) ∧
      (∀ x y : ℝ, 0 < x → 0 < y → f (x * f y) = y * f x) ∧
      Tendsto f atTop (nhds 0)) ↔
    f ∈ Imo1983P1_solution := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo1983P1_refs (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by
  let F : ℝ → ℝ := fun x => if hx : 0 < x then f ⟨x, hx⟩ else 0
  have hFpos : ∀ x : ℝ, 0 < x → 0 < F x := by
    intro x hx
    simp [F, hx, (f ⟨x, hx⟩).property]
  constructor
  · intro hf
    have heq : f = fun x => 1 / x := hf
    constructor
    · intro x y
      rw [heq]
      apply Subtype.ext
      simp
    · intro ε
      refine ⟨⟨1 / ε, by exact div_pos zero_lt_one ε.property⟩, ?_⟩
      intro y hy
      rw [heq]
      change (1 / (y : ℝ)) < (ε : ℝ)
      rw [div_lt_iff₀ y.property]
      have hprod := (div_lt_iff₀ ε.property).1 hy
      simpa [mul_comm] using hprod
  · rintro ⟨hfun, heps⟩
    have hFfun : ∀ x y : ℝ, 0 < x → 0 < y → F (x * F y) = y * F x := by
      intro x y hx hy
      simp only [F, dif_pos hx, dif_pos hy]
      have harg : 0 < x * (f ⟨y, hy⟩ : ℝ) := mul_pos hx (f ⟨y, hy⟩).property
      rw [dif_pos harg]
      exact congrArg Subtype.val (hfun ⟨x, hx⟩ ⟨y, hy⟩)
    have hFlim : Tendsto F atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      let εp : ℝ+ := ⟨ε, hε⟩
      rcases heps εp with ⟨a, ha⟩
      refine ⟨(a : ℝ) + 1, ?_⟩
      intro b hb
      have hab : (a : ℝ) < b := lt_of_lt_of_le (lt_add_one _) hb
      have hbpos : 0 < b := lt_trans a.property hab
      have hlt : f ⟨b, hbpos⟩ < εp := ha ⟨b, hbpos⟩ hab
      have hfpos := (f ⟨b, hbpos⟩).property
      simp only [Real.dist_eq, sub_zero, abs_lt]
      constructor
      · exact lt_trans (neg_lt_zero.mpr hε) (hFpos b hbpos)
      · simpa [F, hbpos] using hlt
    have hFsol : F ∈ Imo1983P1_solution :=
      (Imo1983P1_assumed F).1 ⟨hFpos, hFfun, hFlim⟩
    have hformula : ∀ x : ℝ, 0 < x → F x = 1 / x := hFsol
    apply Set.mem_singleton_iff.mpr
    funext x
    apply Subtype.ext
    simpa [F, x.property] using hformula x x.property
