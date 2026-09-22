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
  let F : ℝ → ℝ := fun x ↦ if hx : 0 < x then f ⟨x, hx⟩ else 0
  have hFpos : ∀ x : ℝ, 0 < x → 0 < F x := by
    intro x hx
    simp [F, hx, (f ⟨x, hx⟩).property]
  constructor
  · intro hf
    have hf' : f = fun x ↦ 1 / x := hf
    have hFmem : F ∈ Imo1983P1_solution := by
      intro x hx
      simp [F, hx, hf']
    obtain ⟨_, hFfun, hFlim⟩ := (Imo1983P1_assumed F).2 hFmem
    constructor
    · intro x y
      apply Subtype.ext
      have h := hFfun (x : ℝ) (y : ℝ) x.property y.property
      rw [show F y = f y by simp [F, y.property]] at h
      rw [show F x = f x by simp [F, x.property]] at h
      rw [show F ((x : ℝ) * (f y : ℝ)) = f (x * f y) by
        dsimp only [F]
        rw [dif_pos (mul_pos x.property (f y).property)]
        exact congrArg (fun z : ℝ+ ↦ (f z : ℝ)) (Subtype.ext (by rfl))] at h
      exact h
    · intro ε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop'.mp hFlim) ε ε.property
      let x : ℝ+ := ⟨max 1 (N + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _)⟩
      refine ⟨x, fun y hxy ↦ ?_⟩
      have hyN : N < (y : ℝ) := lt_trans (lt_add_one N) (lt_of_le_of_lt (le_max_right _ _) hxy)
      have := hN y hyN
      simpa [F, y.property, Real.dist_eq, abs_of_pos (f y).property] using this
  · rintro ⟨hfun, hbound⟩
    have hFfun : ∀ x y : ℝ, 0 < x → 0 < y → F (x * F y) = y * F x := by
      intro x y hx hy
      rw [show F y = f ⟨y, hy⟩ by simp [F, hy]]
      rw [show F x = f ⟨x, hx⟩ by simp [F, hx]]
      rw [show F (x * (f ⟨y, hy⟩ : ℝ)) = f (⟨x, hx⟩ * f ⟨y, hy⟩) by
        dsimp only [F]
        rw [dif_pos (mul_pos hx (f ⟨y, hy⟩).property)]
        exact congrArg (fun z : ℝ+ ↦ (f z : ℝ)) (Subtype.ext (by rfl))]
      exact congrArg Subtype.val (hfun ⟨x, hx⟩ ⟨y, hy⟩)
    have hFlim : Tendsto F atTop (nhds 0) := Metric.tendsto_atTop'.2 (by
      intro ε hε
      obtain ⟨x, hx⟩ := hbound ⟨ε, hε⟩
      refine ⟨x, fun y hy ↦ ?_⟩
      have hypos : 0 < y := lt_trans x.property hy
      have hlt := hx ⟨y, hypos⟩ hy
      simpa [F, hypos, Real.dist_eq, abs_of_pos (f ⟨y, hypos⟩).property] using hlt)
    have hFmem := (Imo1983P1_assumed F).1 ⟨hFpos, hFfun, hFlim⟩
    apply Set.mem_singleton_iff.2
    funext x
    apply Subtype.ext
    have := hFmem x x.property
    simpa [F, x.property, Imo1983P1_solution] using this
