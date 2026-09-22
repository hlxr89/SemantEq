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
  constructor
  · intro hf_mem
    have hF_mem : F ∈ Imo1983P1_solution := by
      change ∀ x : ℝ, 0 < x → F x = 1 / x
      intro x hx
      have h := congrArg Subtype.val (congrFun hf_mem ⟨x, hx⟩)
      simpa [F, hx, SolutionSet] using h
    have hF := (Imo1983P1_assumed F).2 hF_mem
    refine ⟨?_, ?_⟩
    · intro x y
      apply Subtype.ext
      simpa [F, x.property, y.property, (f y).property,
        mul_pos x.property (f y).property] using
        hF.2.1 (x : ℝ) (y : ℝ) x.property y.property
    · intro ε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hF.2.2) ε ε.property
      let x : ℝ+ := ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1)⟩
      refine ⟨x, ?_⟩
      intro y hxy
      have hyN : N ≤ (y : ℝ) := le_trans (le_max_left N 1) (le_of_lt hxy)
      have h := hN (y : ℝ) hyN
      simpa [F, y.property, Real.dist_eq, abs_of_pos (f y).property] using h
  · rintro ⟨hf_eq, hf_tail⟩
    have hF_pos : ∀ x : ℝ, 0 < x → 0 < F x := by
      intro x hx
      simpa [F, hx] using (f ⟨x, hx⟩).property
    have hF_eq : ∀ x y : ℝ, 0 < x → 0 < y → F (x * F y) = y * F x := by
      intro x y hx hy
      have h := congrArg Subtype.val (hf_eq ⟨x, hx⟩ ⟨y, hy⟩)
      simpa [F, hx, hy, (f ⟨y, hy⟩).property,
        mul_pos hx (f ⟨y, hy⟩).property] using h
    have hF_lim : Tendsto F atTop (nhds 0) := by
      apply Metric.tendsto_atTop.2
      intro ε hε
      obtain ⟨x, hx⟩ := hf_tail ⟨ε, hε⟩
      refine ⟨(x : ℝ) + 1, ?_⟩
      intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le x.property (le_trans (le_add_of_nonneg_right zero_le_one) hy)
      have hxy : x < (⟨y, hy_pos⟩ : ℝ+) := by
        change (x : ℝ) < y
        exact lt_of_lt_of_le (lt_add_one (x : ℝ)) hy
      have h := hx ⟨y, hy_pos⟩ hxy
      simpa [F, hy_pos, Real.dist_eq, abs_of_pos (f ⟨y, hy_pos⟩).property] using h
    have hF_mem : F ∈ Imo1983P1_solution :=
      (Imo1983P1_assumed F).1 ⟨hF_pos, hF_eq, hF_lim⟩
    change f = fun x => 1 / x
    funext x
    apply Subtype.ext
    have h := hF_mem (x : ℝ) x.property
    simpa [F, x.property, Imo1983P1_solution] using h
