import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

def SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

def Imo1983P1_solution : Set (ℝ → ℝ) := {f | ∀ x : ℝ, 0 < x → f x = 1 / x}

-- ===== assumed statement (antecedent) =====
theorem Imo1983P1_refs_assumed (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Imo1983P1 (f : ℝ → ℝ) (hf_pos : ∀ x : ℝ, 0 < x → 0 < f x) :
    ((∀ x y : ℝ, 0 < x → 0 < y → f (x * f y) = y * f x) ∧
      Tendsto f atTop (nhds 0)) ↔
    f ∈ Imo1983P1_solution := by
  constructor
  · rintro ⟨hf_eq, hf_lim⟩
    let g : ℝ+ → ℝ+ := fun x => ⟨f x, hf_pos x x.property⟩
    have hiff := Imo1983P1_refs_assumed g
    have hg_eq : ∀ x y, g (x * g y) = y * g x := by
      intro x y
      apply Subtype.ext
      exact hf_eq x y x.property y.property
    have hg_tail : ∀ ε, ∃ x, ∀ y, x < y → g y < ε := by
      intro ε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hf_lim) ε ε.property
      refine ⟨⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1)⟩, ?_⟩
      intro y hxy
      change f y < ε
      have hyN : N ≤ (y : ℝ) := le_trans (le_max_left N 1) (le_of_lt hxy)
      simpa [Real.dist_eq, abs_of_pos (hf_pos y y.property)] using hN y hyN
    have himp := hiff.mpr
    have hg_mem := himp ⟨hg_eq, hg_tail⟩
    change ∀ x : ℝ, 0 < x → f x = 1 / x
    intro x hx
    exact congrArg Subtype.val (congrFun hg_mem ⟨x, hx⟩)
  · intro hf_mem
    change ∀ x : ℝ, 0 < x → f x = 1 / x at hf_mem
    let g : ℝ+ → ℝ+ := fun x => 1 / x
    have hiff := Imo1983P1_refs_assumed g
    have hmp := hiff.mp
    have hg := hmp rfl
    refine ⟨?_, ?_⟩
    · intro x y hx hy
      have h := congrArg Subtype.val (hg.1 ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hf_mem y hy, hf_mem x hx,
        hf_mem (x * (1 / y)) (mul_pos hx (one_div_pos.mpr hy))]
      exact h
    · apply Metric.tendsto_atTop.2
      intro ε hε
      obtain ⟨x, hx⟩ := hg.2 ⟨ε, hε⟩
      refine ⟨(x : ℝ) + 1, ?_⟩
      intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le x.property (le_trans (le_add_of_nonneg_right zero_le_one) hy)
      have hxy : x < (⟨y, hy_pos⟩ : ℝ+) := by
        change (x : ℝ) < y
        exact lt_of_lt_of_le (lt_add_one (x : ℝ)) hy
      have htail := hx ⟨y, hy_pos⟩ hxy
      have htail' : (1 / y : ℝ) < ε := by
        exact_mod_cast htail
      rw [hf_mem y hy_pos, Real.dist_eq, sub_zero,
        abs_of_pos (one_div_pos.mpr hy_pos)]
      exact htail'
