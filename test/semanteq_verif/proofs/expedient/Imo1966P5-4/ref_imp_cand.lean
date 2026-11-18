import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 10000

-- ===== unified context (both sides' local defs, merged) =====
noncomputable def raw_order {n : ℕ} (a : Fin n → ℝ) : Fin n → ℕ :=
  fun i ↦ Finset.card {j | a j < a i}

lemma raw_order_lt {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
  : raw_order a i < n := by
  rw [raw_order, ]
  apply lt_of_le_of_ne
  · apply card_finset_fin_le
  · simp only [← Finset.card_fin n]
    rw [ne_eq, Finset.card_filter_eq_iff]
    push Not
    use i
    constructor
    · apply Finset.mem_univ
    · rfl

noncomputable def order {n : ℕ} (a : Fin n → ℝ) : Fin n → Fin n :=
  fun i ↦ ⟨raw_order a i, raw_order_lt a i⟩

lemma bijective_order {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Function.Bijective (order a) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    contrapose! hij
    wlog hij' : a i < a j generalizing i j
    · symm
      apply this hij.symm
      exact lt_of_le_of_ne (not_lt.mp hij') (Ne.symm (ha.ne hij))
    apply ne_of_lt
    simp only [order, raw_order, Fin.mk_lt_mk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_exists_cons_subset]
    use i
    constructor
    · simp
      rw [Finset.insert_subset_iff]
      constructor
      · simp
        exact hij'
      · intro k hk
        simp at hk ⊢
        exact lt_trans hk hij'
    · simp
  · rfl

noncomputable def nth_smallest_index {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Fin n → Fin n :=
  Fintype.bijInv (bijective_order ha)

noncomputable def nth_smallest {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Fin n → ℝ := a ∘ (nth_smallest_index ha)

noncomputable def solution_set_generalized {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : Function.Injective a) : Set ((Fin n → ℝ)) := {
    fun i : Fin n ↦
      if order a i = ⟨0, by lia⟩ ∨ order a i = ⟨n - 1, by lia⟩
      then 1 / (nth_smallest ha ⟨n - 1, by lia⟩ - nth_smallest ha ⟨0, by lia⟩)
      else 0
  }

noncomputable abbrev solution_set {a : Fin 4 → ℝ}
    (ha : Function.Injective a) : Set ((Fin 4 → ℝ)) :=
  solution_set_generalized (by norm_num : 2 ≤ 4) ha

-- ===== assumed statement (antecedent) =====
theorem imo1966_p5_assumed
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (a₁ a₂ a₃ a₄ : ℝ),
    a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄ ∧ a₃ ≠ a₄ →
    ∃! (x : Fin 4 → ℝ),
      (|a₁ - a₂| * x 1 + |a₁ - a₃| * x 2 + |a₁ - a₄| * x 3 = 1) ∧
      (|a₂ - a₁| * x 0 + |a₂ - a₃| * x 2 + |a₂ - a₄| * x 3 = 1) ∧
      (|a₃ - a₁| * x 0 + |a₃ - a₂| * x 1 + |a₃ - a₄| * x 3 = 1) ∧
      (|a₄ - a₁| * x 0 + |a₄ - a₂| * x 1 + |a₄ - a₃| * x 2 = 1) ∧
      ∃ (M m : ℝ) (i_max i_min : Fin 4),
        M = max (max a₁ (max a₂ a₃)) a₄ ∧
        m = min (min a₁ (min a₂ a₃)) a₄ ∧
        (i_max = 0 ∧ a₁ = M ∨ i_max = 1 ∧ a₂ = M ∨ i_max = 2 ∧ a₃ = M ∨ i_max = 3 ∧ a₄ = M) ∧
        (i_min = 0 ∧ a₁ = m ∨ i_min = 1 ∧ a₂ = m ∨ i_min = 2 ∧ a₃ = m ∨ i_min = 3 ∧ a₄ = m) ∧
        i_max ≠ i_min ∧
        (i_max = 0 → x 0 = 1 / (M - m)) ∧
        (i_max = 1 → x 1 = 1 / (M - m)) ∧
        (i_max = 2 → x 2 = 1 / (M - m)) ∧
        (i_max = 3 → x 3 = 1 / (M - m)) ∧
        (i_min = 0 → x 0 = 1 / (M - m)) ∧
        (i_min = 1 → x 1 = 1 / (M - m)) ∧
        (i_min = 2 → x 2 = 1 / (M - m)) ∧
        (i_min = 3 → x 3 = 1 / (M - m)) ∧
        (i_max ≠ 0 ∧ i_min ≠ 0 → x 0 = 0) ∧
        (i_max ≠ 1 ∧ i_min ≠ 1 → x 1 = 0) ∧
        (i_max ≠ 2 ∧ i_min ≠ 2 → x 2 = 0) ∧
        (i_max ≠ 3 ∧ i_min ≠ 3 → x 3 = 0) := by
  -- not proved: exhaustive strict-order simplification did not elaborate within a practical compilation time
  sorry
