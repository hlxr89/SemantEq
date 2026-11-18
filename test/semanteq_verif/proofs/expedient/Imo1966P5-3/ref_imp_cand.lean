import Mathlib

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

def max_of_four (a₁ a₂ a₃ a₄ : ℝ) : ℝ := max a₁ (max a₂ (max a₃ a₄))
def min_of_four (a₁ a₂ a₃ a₄ : ℝ) : ℝ := min a₁ (min a₂ (min a₃ a₄))

-- ===== assumed statement (antecedent) =====
theorem imo1966_p5_assumed
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement 
  (a₁ a₂ a₃ a₄ : ℝ) 
  (h_distinct : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄ ∧ a₃ ≠ a₄) :
  ∃! (p : ℝ × ℝ × ℝ × ℝ),
    let (x₁, x₂, x₃, x₄) := p
    |a₁ - a₂| * x₂ + |a₁ - a₃| * x₃ + |a₁ - a₄| * x₄ = 1 ∧
    |a₂ - a₁| * x₁ + |a₂ - a₃| * x₃ + |a₂ - a₄| * x₄ = 1 ∧
    |a₃ - a₁| * x₁ + |a₃ - a₂| * x₂ + |a₃ - a₄| * x₄ = 1 ∧
    |a₄ - a₁| * x₁ + |a₄ - a₂| * x₂ + |a₄ - a₃| * x₃ = 1 ∧
    let M := max_of_four a₁ a₂ a₃ a₄
    let m := min_of_four a₁ a₂ a₃ a₄
    (if a₁ = M then
      (if a₂ = m then (x₁ = 1 / (M - m) ∧ x₂ = 1 / (M - m) ∧ x₃ = 0 ∧ x₄ = 0)
       else if a₃ = m then (x₁ = 1 / (M - m) ∧ x₂ = 0 ∧ x₃ = 1 / (M - m) ∧ x₄ = 0)
       else if a₄ = m then (x₁ = 1 / (M - m) ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 1 / (M - m))
       else False)
    else if a₂ = M then
      (if a₁ = m then (x₁ = 1 / (M - m) ∧ x₂ = 1 / (M - m) ∧ x₃ = 0 ∧ x₄ = 0)
       else if a₃ = m then (x₁ = 0 ∧ x₂ = 1 / (M - m) ∧ x₃ = 1 / (M - m) ∧ x₄ = 0)
       else if a₄ = m then (x₁ = 0 ∧ x₂ = 1 / (M - m) ∧ x₃ = 0 ∧ x₄ = 1 / (M - m))
       else False)
    else if a₃ = M then
      (if a₁ = m then (x₁ = 1 / (M - m) ∧ x₂ = 0 ∧ x₃ = 1 / (M - m) ∧ x₄ = 0)
       else if a₂ = m then (x₁ = 0 ∧ x₂ = 1 / (M - m) ∧ x₃ = 1 / (M - m) ∧ x₄ = 0)
       else if a₄ = m then (x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 1 / (M - m) ∧ x₄ = 1 / (M - m))
       else False)
    else -- a₄ = M
      (if a₁ = m then (x₁ = 1 / (M - m) ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 1 / (M - m))
       else if a₂ = m then (x₁ = 0 ∧ x₂ = 1 / (M - m) ∧ x₃ = 0 ∧ x₄ = 1 / (M - m))
       else if a₃ = m then (x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 1 / (M - m) ∧ x₄ = 1 / (M - m))
       else False)) := by
  -- not proved: requires bridging rank-based Fin 4 endpoints with nested min/max cases
  sorry

