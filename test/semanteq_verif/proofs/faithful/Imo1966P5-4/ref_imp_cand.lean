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
  classical
  intro a₁ a₂ a₃ a₄ hne
  let a : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have ha : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  let i_min : Fin 4 := nth_smallest_index ha 0
  let i_max : Fin 4 := nth_smallest_index ha 3
  have hmin_order : order a i_min = 0 := by
    exact Fintype.rightInverse_bijInv (bijective_order ha) 0
  have hmax_order : order a i_max = 3 := by
    exact Fintype.rightInverse_bijInv (bijective_order ha) 3
  have horder_strict {i j : Fin 4} (hij : a i < a j) : order a i < order a j := by
    simp only [order, raw_order, Fin.mk_lt_mk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_exists_cons_subset]
    use i
    constructor
    · simp
      rw [Finset.insert_subset_iff]
      constructor
      · simp [hij]
      · intro k hk
        simp at hk ⊢
        exact lt_trans hk hij
    · simp
  have hmax (i : Fin 4) : a i ≤ a i_max := by
    by_contra h
    have hai : a i_max < a i := lt_of_not_ge h
    have := horder_strict hai
    rw [hmax_order] at this
    exact (not_lt_of_ge (Fin.le_last _)) this
  have hmin (i : Fin 4) : a i_min ≤ a i := by
    by_contra h
    have hai : a i < a i_min := lt_of_not_ge h
    have := horder_strict hai
    rw [hmin_order] at this
    exact (not_lt_of_ge (Fin.zero_le _)) this
  have himax_ne_imin : i_max ≠ i_min := by
    intro h
    rw [h] at hmax_order
    have : (0 : Fin 4) = 3 := hmin_order.symm.trans hmax_order
    have := congrArg Fin.val this
    norm_num at this
  have hfin (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    omega
  have hmax0 : a₁ ≤ a i_max := by simpa [a] using hmax 0
  have hmax1 : a₂ ≤ a i_max := by simpa [a] using hmax 1
  have hmax2 : a₃ ≤ a i_max := by simpa [a] using hmax 2
  have hmax3 : a₄ ≤ a i_max := by simpa [a] using hmax 3
  have hmin0 : a i_min ≤ a₁ := by simpa [a] using hmin 0
  have hmin1 : a i_min ≤ a₂ := by simpa [a] using hmin 1
  have hmin2 : a i_min ≤ a₃ := by simpa [a] using hmin 2
  have hmin3 : a i_min ≤ a₄ := by simpa [a] using hmin 3
  let x : Fin 4 → ℝ := fun i ↦
    if order a i = (0 : Fin 4) ∨ order a i = (3 : Fin 4)
    then 1 / (nth_smallest ha 3 - nth_smallest ha 0)
    else 0
  have hxmem : x ∈ solution_set ha := by
    rfl
  have hsys := (imo1966_p5_assumed x a ha).2 hxmem
  have heq0 := hsys (0 : Fin 4)
  have heq1 := hsys (1 : Fin 4)
  have heq2 := hsys (2 : Fin 4)
  have heq3 := hsys (3 : Fin 4)
  simp only [Fin.sum_univ_four] at heq0 heq1 heq2 heq3
  simp [a] at heq0 heq1 heq2 heq3
  have hxmax : x i_max = 1 / (a i_max - a i_min) := by
    simp only [x, if_pos (Or.inr hmax_order)]
    rfl
  have hxmin : x i_min = 1 / (a i_max - a i_min) := by
    simp only [x, if_pos (Or.inl hmin_order)]
    rfl
  have hxzero (i : Fin 4) (hni_max : i_max ≠ i) (hni_min : i_min ≠ i) : x i = 0 := by
    rw [show x i = if order a i = (0 : Fin 4) ∨ order a i = 3
        then 1 / (nth_smallest ha 3 - nth_smallest ha 0) else 0 by rfl]
    rw [if_neg]
    intro hi
    rcases hi with hi | hi
    · exact hni_min ((bijective_order ha).1 (hmin_order.trans hi.symm))
    · exact hni_max ((bijective_order ha).1 (hmax_order.trans hi.symm))
  refine ⟨x, ?_, ?_⟩
  · refine ⟨heq0, heq1, heq2, heq3, ?_⟩
    refine ⟨a i_max, a i_min, i_max, i_min, ?_, ?_, ?_, ?_, himax_ne_imin, ?_⟩
    · rcases hfin i_max with h | h | h | h <;>
        rw [h] at hmax0 hmax1 hmax2 hmax3 ⊢ <;>
        simp [a] at hmax0 hmax1 hmax2 hmax3 <;>
        simp_all [a, max_eq_left]
    · rcases hfin i_min with h | h | h | h <;>
        rw [h] at hmin0 hmin1 hmin2 hmin3 ⊢ <;>
        simp [a] at hmin0 hmin1 hmin2 hmin3 <;>
        simp_all [a, min_eq_left]
    · rcases hfin i_max with h | h | h | h <;> simp [h, a]
    · rcases hfin i_min with h | h | h | h <;> simp [h, a]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h; simpa [h] using hxmax
      · intro h; simpa [h] using hxmax
      · intro h; simpa [h] using hxmax
      · intro h; simpa [h] using hxmax
      · intro h; simpa [h] using hxmin
      · intro h; simpa [h] using hxmin
      · intro h; simpa [h] using hxmin
      · intro h; simpa [h] using hxmin
      · rintro ⟨h₁, h₂⟩; exact hxzero 0 h₁ h₂
      · rintro ⟨h₁, h₂⟩; exact hxzero 1 h₁ h₂
      · rintro ⟨h₁, h₂⟩; exact hxzero 2 h₁ h₂
      · rintro ⟨h₁, h₂⟩; exact hxzero 3 h₁ h₂
  · intro y hy
    have hysys : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * y j = 1 := by
      intro i
      fin_cases i
      · simpa [Fin.sum_univ_four, a] using hy.1
      · simpa [Fin.sum_univ_four, a] using hy.2.1
      · simpa [Fin.sum_univ_four, a] using hy.2.2.1
      · simpa [Fin.sum_univ_four, a] using hy.2.2.2.1
    have hymem := (imo1966_p5_assumed y a ha).1 hysys
    exact hymem.trans hxmem.symm
