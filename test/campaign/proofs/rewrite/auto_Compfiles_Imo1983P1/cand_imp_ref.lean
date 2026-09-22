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
  let F : ℝ → ℝ := fun x ↦ if hx : 0 < x then (f ⟨x, hx⟩ : ℝ+) else 0
  have hFpos : ∀ x : ℝ, 0 < x → 0 < F x := by
    intro x hx
    simp only [F, dif_pos hx]
    exact (f ⟨x, hx⟩).property
  constructor
  · intro hf
    have hFsol : F ∈ Imo1983P1_solution := by
      change ∀ x : ℝ, 0 < x → F x = 1 / x
      intro x hx
      change f = (fun z : ℝ+ ↦ 1 / z) at hf
      have hv := congrArg Subtype.val (congrFun hf (⟨x, hx⟩ : ℝ+))
      simpa only [F, dif_pos hx] using hv
    obtain ⟨_, hFfun, hFlim⟩ := (Imo1983P1_assumed F).2 hFsol
    constructor
    · intro x y
      have hv := hFfun x y x.property y.property
      have hxy : 0 < (x : ℝ) * (f y : ℝ) := mul_pos x.property (f y).property
      apply Subtype.ext
      simp only [F, dif_pos x.property, dif_pos y.property, dif_pos hxy] at hv
      exact hv
    · intro ε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hFlim) ε ε.property
      let x : ℝ+ := ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1)⟩
      refine ⟨x, ?_⟩
      intro y hxy
      have hNy : N ≤ (y : ℝ) := le_trans (le_max_left N 1) (le_of_lt hxy)
      have hydist := hN y hNy
      simpa only [F, dif_pos y.property, Real.dist_eq, sub_zero,
        abs_of_pos (f y).property] using hydist
  · rintro ⟨hfun, heps⟩
    have hFfun : ∀ x y : ℝ, 0 < x → 0 < y → F (x * F y) = y * F x := by
      intro x y hx hy
      have hv := congrArg Subtype.val (hfun (⟨x, hx⟩ : ℝ+) (⟨y, hy⟩ : ℝ+))
      have hxy : 0 < x * (f (⟨y, hy⟩ : ℝ+) : ℝ) := mul_pos hx (f ⟨y, hy⟩).property
      simp only [F, dif_pos hx, dif_pos hy, dif_pos hxy]
      exact hv
    have hFlim : Tendsto F atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨X, hX⟩ := heps (⟨ε, hε⟩ : ℝ+)
      refine ⟨(X : ℝ) + 1, ?_⟩
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le (lt_trans X.property (lt_add_one (X : ℝ))) hn
      have hXn_real : (X : ℝ) < n := lt_of_lt_of_le (lt_add_one (X : ℝ)) hn
      have hXn : X < (⟨n, hnpos⟩ : ℝ+) := hXn_real
      have hv := hX (⟨n, hnpos⟩ : ℝ+) hXn
      simpa only [F, dif_pos hnpos, Real.dist_eq, sub_zero,
        abs_of_pos (f ⟨n, hnpos⟩).property] using hv
    have hFsol := (Imo1983P1_assumed F).1 ⟨hFpos, hFfun, hFlim⟩
    change ∀ x : ℝ, 0 < x → F x = 1 / x at hFsol
    change f = fun z : ℝ+ ↦ 1 / z
    funext z
    apply Subtype.ext
    simpa only [F, dif_pos z.property] using hFsol z z.property
