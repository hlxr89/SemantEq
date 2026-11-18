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
    let M := max (max a₁ a₂) (max a₃ a₄)
    let m := min (min a₁ a₂) (min a₃ a₄)
    let M_minus_m := M - m
    ∃! (x : Fin 4 → ℝ),
      (abs (a₁ - a₂) * x 1 + abs (a₁ - a₃) * x 2 + abs (a₁ - a₄) * x 3 = 1) ∧
      (abs (a₂ - a₁) * x 0 + abs (a₂ - a₃) * x 2 + abs (a₂ - a₄) * x 3 = 1) ∧
      (abs (a₃ - a₁) * x 0 + abs (a₃ - a₂) * x 1 + abs (a₃ - a₄) * x 3 = 1) ∧
      (abs (a₄ - a₁) * x 0 + abs (a₄ - a₂) * x 1 + abs (a₄ - a₃) * x 2 = 1) ∧
      (∃ (i j : Fin 4), i ≠ j ∧ 
        x i = 1 / M_minus_m ∧ x j = 1 / M_minus_m ∧
        ∀ k : Fin 4, k ≠ i ∧ k ≠ j → x k = 0) := by
  intro a₁ a₂ a₃ a₄ hne
  let a : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have ha : Function.Injective a := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [a] <;> aesop
  let x : Fin 4 → ℝ := fun i ↦
    if order a i = ⟨0, by lia⟩ ∨ order a i = ⟨4 - 1, by lia⟩
    then 1 / (nth_smallest ha ⟨4 - 1, by lia⟩ - nth_smallest ha ⟨0, by lia⟩)
    else 0
  have hxmem : x ∈ solution_set ha := by
    rfl
  have heq := (imo1966_p5_assumed x a ha).2 hxmem
  have e₀ := heq (0 : Fin 4)
  have e₁ := heq (1 : Fin 4)
  have e₂ := heq (2 : Fin 4)
  have e₃ := heq (3 : Fin 4)
  simp [Fin.sum_univ_four, a] at e₀ e₁ e₂ e₃
  have hord_lt {i j : Fin 4} (hij : a i < a j) : order a i < order a j := by
    simp only [order, raw_order, Fin.mk_lt_mk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_exists_cons_subset]
    use i
    constructor
    · simp
      rw [Finset.insert_subset_iff]
      constructor
      · simpa
      · intro k hk
        simp at hk ⊢
        exact lt_trans hk hij
    · simp
  let i₀ : Fin 4 := nth_smallest_index ha 0
  let i₃ : Fin 4 := nth_smallest_index ha 3
  have hi₀ : order a i₀ = 0 := Fintype.rightInverse_bijInv (bijective_order ha) 0
  have hi₃ : order a i₃ = 3 := Fintype.rightInverse_bijInv (bijective_order ha) 3
  have hmin (j : Fin 4) : a i₀ ≤ a j := by
    by_contra h
    have := hord_lt (lt_of_not_ge h)
    rw [hi₀] at this
    omega
  have hmax (j : Fin 4) : a j ≤ a i₃ := by
    by_contra h
    have := hord_lt (lt_of_not_ge h)
    rw [hi₃] at this
    omega
  have hMin : min (min a₁ a₂) (min a₃ a₄) = a i₀ := by
    apply le_antisymm
    · have hi : i₀ = 0 ∨ i₀ = 1 ∨ i₀ = 2 ∨ i₀ = 3 := by omega
      rcases hi with hi | hi | hi | hi <;> rw [hi] <;> simp [a]
    · simp only [le_min_iff]
      exact ⟨⟨hmin 0, hmin 1⟩, hmin 2, hmin 3⟩
  have hMax : max (max a₁ a₂) (max a₃ a₄) = a i₃ := by
    apply le_antisymm
    · simp only [max_le_iff]
      exact ⟨⟨hmax 0, hmax 1⟩, hmax 2, hmax 3⟩
    · have hi : i₃ = 0 ∨ i₃ = 1 ∨ i₃ = 2 ∨ i₃ = 3 := by omega
      rcases hi with hi | hi | hi | hi <;> rw [hi] <;> simp [a]
  have hnth₀ : nth_smallest ha 0 = a i₀ := rfl
  have hnth₃ : nth_smallest ha 3 = a i₃ := rfl
  have hi_ne : i₀ ≠ i₃ := by
    intro h
    have := congrArg (order a) h
    rw [hi₀, hi₃] at this
    omega
  have hx₀ : x i₀ = 1 / (max (max a₁ a₂) (max a₃ a₄) - min (min a₁ a₂) (min a₃ a₄)) := by
    simp [x, hi₀, hnth₀, hnth₃, hMin, hMax]
  have hx₃ : x i₃ = 1 / (max (max a₁ a₂) (max a₃ a₄) - min (min a₁ a₂) (min a₃ a₄)) := by
    simp [x, hi₃, hnth₀, hnth₃, hMin, hMax]
  have hx_other (k : Fin 4) (hk₀ : k ≠ i₀) (hk₃ : k ≠ i₃) : x k = 0 := by
    have hk : ¬(order a k = 0 ∨ order a k = 3) := by
      rintro (hk | hk)
      · exact hk₀ ((bijective_order ha).1 (hk.trans hi₀.symm))
      · exact hk₃ ((bijective_order ha).1 (hk.trans hi₃.symm))
    simp [x, hk]
  refine ⟨x, ?_, ?_⟩
  · exact ⟨e₀, e₁, e₂, e₃, ⟨i₀, i₃, hi_ne, hx₀, hx₃, fun k hk ↦ hx_other k hk.1 hk.2⟩⟩
  · intro y hy
    apply Set.mem_singleton_iff.mp
    exact (imo1966_p5_assumed y a ha).1 (by
      intro i
      fin_cases i
      · simpa [Fin.sum_univ_four, a] using hy.1
      · simpa [Fin.sum_univ_four, a] using hy.2.1
      · simpa [Fin.sum_univ_four, a] using hy.2.2.1
      · simpa [Fin.sum_univ_four, a] using hy.2.2.2.1)
