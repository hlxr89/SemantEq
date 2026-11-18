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
  dsimp only
  let a : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have ha : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  let lo : Fin 4 := nth_smallest_index ha 0
  let hi : Fin 4 := nth_smallest_index ha 3
  have hlo : order a lo = 0 := by
    exact Fintype.rightInverse_bijInv (bijective_order ha) 0
  have hhi : order a hi = 3 := by
    exact Fintype.rightInverse_bijInv (bijective_order ha) 3
  have hrank_lt : ∀ {i j : Fin 4}, a i < a j → order a i < order a j := by
    intro i j hij
    simp only [order, raw_order, Fin.mk_lt_mk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_exists_cons_subset]
    use i
    constructor
    · simp
      rw [Finset.insert_subset_iff]
      constructor
      · simp
        exact hij
      · intro k hk
        simp at hk ⊢
        exact lt_trans hk hij
    · simp
  have hlo_all : ∀ k : Fin 4, a lo ≤ a k := by
    intro k
    apply not_lt.mp
    intro hk
    have hh := hrank_lt hk
    rw [hlo] at hh
    exact (Fin.not_lt_zero _ hh)
  have hhi_all : ∀ k : Fin 4, a k ≤ a hi := by
    intro k
    apply not_lt.mp
    intro hk
    have hh := hrank_lt hk
    rw [hhi] at hh
    exact (Nat.not_lt_of_ge (Fin.le_last (order a k))) hh
  have ha_cases (i : Fin 4) : a i = a₁ ∨ a i = a₂ ∨ a i = a₃ ∨ a i = a₄ := by
    fin_cases i <;> simp [a]
  have hlo_value : nth_smallest ha 0 = min (min a₁ a₂) (min a₃ a₄) := by
    change a lo = _
    apply le_antisymm
    · exact le_min (le_min (hlo_all 0) (hlo_all 1)) (le_min (hlo_all 2) (hlo_all 3))
    · rcases ha_cases lo with h | h | h | h <;> rw [h] <;> simp
  have hhi_value : nth_smallest ha 3 = max (max a₁ a₂) (max a₃ a₄) := by
    change a hi = _
    apply le_antisymm
    · rcases ha_cases hi with h | h | h | h <;> rw [h] <;> simp
    · exact max_le (max_le (hhi_all 0) (hhi_all 1)) (max_le (hhi_all 2) (hhi_all 3))
  let x : Fin 4 → ℝ := fun i ↦
    if order a i = 0 ∨ order a i = 3
    then 1 / (nth_smallest ha 3 - nth_smallest ha 0)
    else 0
  have hxmem : x ∈ solution_set ha := by
    simp only [solution_set, solution_set_generalized, Set.mem_singleton_iff]
    funext i
    simp only [x]
    congr 2 <;> norm_num
  have hxsum := (imo1966_p5_assumed x a ha).mpr hxmem
  have hxsys :
      (abs (a₁ - a₂) * x 1 + abs (a₁ - a₃) * x 2 + abs (a₁ - a₄) * x 3 = 1) ∧
      (abs (a₂ - a₁) * x 0 + abs (a₂ - a₃) * x 2 + abs (a₂ - a₄) * x 3 = 1) ∧
      (abs (a₃ - a₁) * x 0 + abs (a₃ - a₂) * x 1 + abs (a₃ - a₄) * x 3 = 1) ∧
      (abs (a₄ - a₁) * x 0 + abs (a₄ - a₂) * x 1 + abs (a₄ - a₃) * x 2 = 1) := by
    simpa only [a, Fin.sum_univ_four, sub_self, abs_zero, zero_mul, zero_add,
      add_zero, Fin.isValue] using And.intro (hxsum 0)
        (And.intro (hxsum 1) (And.intro (hxsum 2) (hxsum 3)))
  have hlohi : lo ≠ hi := by
    intro heq
    rw [heq, hhi] at hlo
    have hval := congrArg Fin.val hlo
    norm_num at hval
  have hxsupport : ∃ (i j : Fin 4), i ≠ j ∧
      x i = 1 / (max (max a₁ a₂) (max a₃ a₄) - min (min a₁ a₂) (min a₃ a₄)) ∧
      x j = 1 / (max (max a₁ a₂) (max a₃ a₄) - min (min a₁ a₂) (min a₃ a₄)) ∧
      ∀ k : Fin 4, k ≠ i ∧ k ≠ j → x k = 0 := by
    refine ⟨lo, hi, hlohi, ?_, ?_, ?_⟩
    · simp only [x, hlo, true_or, if_true, hhi_value, hlo_value]
    · simp only [x, hhi, or_true, if_true, hhi_value, hlo_value]
    · intro k hk
      simp only [x]
      rw [if_neg]
      intro hor
      rcases hor with hk0 | hk3
      · apply hk.1
        exact (bijective_order ha).1 (hk0.trans hlo.symm)
      · apply hk.2
        exact (bijective_order ha).1 (hk3.trans hhi.symm)
  refine ⟨x, ⟨hxsys.1, hxsys.2.1, hxsys.2.2.1, hxsys.2.2.2, hxsupport⟩, ?_⟩
  intro y hy
  apply Set.mem_singleton_iff.mp
  apply (imo1966_p5_assumed y a ha).mp
  intro i
  fin_cases i
  · simpa [a, Fin.sum_univ_four] using hy.1
  · simpa [a, Fin.sum_univ_four] using hy.2.1
  · simpa [a, Fin.sum_univ_four] using hy.2.2.1
  · simpa [a, Fin.sum_univ_four] using hy.2.2.2.1
