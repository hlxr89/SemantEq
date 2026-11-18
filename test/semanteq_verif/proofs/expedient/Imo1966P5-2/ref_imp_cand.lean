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
  intro a₁ a₂ a₃ a₄ h
  rcases h with ⟨h12, h13, h14, h23, h24, h34⟩
  let a : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have ha : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  let x : Fin 4 → ℝ := fun i ↦
    if order a i = ⟨0, by lia⟩ ∨ order a i = ⟨4 - 1, by lia⟩
    then 1 / (nth_smallest ha ⟨4 - 1, by lia⟩ - nth_smallest ha ⟨0, by lia⟩)
    else 0
  have hxmem : x ∈ solution_set ha := by
    rfl
  have hx := (imo1966_p5_assumed x a ha).2 hxmem
  dsimp only
  simp only [Fin.sum_univ_four] at hx
  simp [a] at hx
  all_goals
    let i : Fin 4 := nth_smallest_index ha ⟨0, by omega⟩
    let j : Fin 4 := nth_smallest_index ha ⟨3, by omega⟩
    have hi : order a i = ⟨0, by omega⟩ :=
      Fintype.rightInverse_bijInv (bijective_order ha) ⟨0, by omega⟩
    have hj : order a j = ⟨3, by omega⟩ :=
      Fintype.rightInverse_bijInv (bijective_order ha) ⟨3, by omega⟩
    have hij : i ≠ j := by
      intro e
      have he := congrArg (order a) e
      rw [hi, hj] at he
      norm_num at he
    have hmin : nth_smallest ha ⟨0, by omega⟩ = min (min a₁ a₂) (min a₃ a₄) := by
      change a i = _
      have hle : ∀ q : Fin 4, a i ≤ a q := by
        simpa [order, raw_order] using hi
      apply le_antisymm
      · exact le_min (le_min (hle 0) (hle 1)) (le_min (hle 2) (hle 3))
      · have hall : ∀ q : Fin 4, min (min a₁ a₂) (min a₃ a₄) ≤ a q := by
          intro q
          fin_cases q <;> simp [a]
        exact hall i
    have hmax : nth_smallest ha ⟨3, by omega⟩ = max (max a₁ a₂) (max a₃ a₄) := by
      change a j = _
      have hmono : ∀ p q : Fin 4, a p < a q → order a p < order a q := by
        intro p q hpq
        simp only [order, raw_order, Fin.mk_lt_mk]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_exists_cons_subset]
        use p
        constructor
        · simp
          rw [Finset.insert_subset_iff]
          constructor
          · simp
            exact hpq
          · intro r hr
            simp at hr ⊢
            exact lt_trans hr hpq
        · simp
      have hge : ∀ q : Fin 4, a q ≤ a j := by
        intro q
        by_contra hn
        have hlt : a j < a q := lt_of_not_ge hn
        have hltorder := hmono j q hlt
        rw [hj] at hltorder
        change 3 < (order a q).val at hltorder
        have hq := (order a q).isLt
        omega
      apply le_antisymm
      · have hall : ∀ q : Fin 4, a q ≤ max (max a₁ a₂) (max a₃ a₄) := by
          intro q
          fin_cases q <;> simp [a]
        exact hall j
      · exact max_le (max_le (hge 0) (hge 1)) (max_le (hge 2) (hge 3))
    have hden : nth_smallest ha ⟨3, by omega⟩ - nth_smallest ha ⟨0, by omega⟩ =
        max (max a₁ a₂) (max a₃ a₄) - min (min a₁ a₂) (min a₃ a₄) := by
      rw [hmax, hmin]
    refine ⟨x, ?_, ?_⟩
    · constructor
      · simpa [abs_sub_comm] using hx 0
      constructor
      · simpa [abs_sub_comm] using hx 1
      constructor
      · simpa [abs_sub_comm] using hx 2
      constructor
      · simpa [abs_sub_comm] using hx 3
      · refine ⟨i, j, hij, ?_, ?_, ?_⟩
        · dsimp [x]
          rw [if_pos]
          exact congrArg (fun z : ℝ => 1 / z) hden
          exact Or.inl (by simpa using hi)
        · dsimp [x]
          rw [if_pos]
          exact congrArg (fun z : ℝ => 1 / z) hden
          exact Or.inr (by simpa using hj)
        · intro k hk
          have hk0 : order a k ≠ ⟨0, by omega⟩ := by
            intro heq
            apply hk.1
            exact (bijective_order ha).1 (heq.trans hi.symm)
          have hk3 : order a k ≠ ⟨3, by omega⟩ := by
            intro heq
            apply hk.2
            exact (bijective_order ha).1 (heq.trans hj.symm)
          dsimp [x]
          rw [if_neg]
          intro hor
          rcases hor with hor | hor
          · exact hk0 (by simpa using hor)
          · exact hk3 (by simpa using hor)
    · intro y hy
      have hyeq : ∀ q : Fin 4, ∑ r : Fin 4, abs (a q - a r) * y r = 1 := by
        intro q
        fin_cases q
        · simpa [Fin.sum_univ_four, a, abs_sub_comm] using hy.1
        · simpa [Fin.sum_univ_four, a, abs_sub_comm] using hy.2.1
        · simpa [Fin.sum_univ_four, a, abs_sub_comm] using hy.2.2.1
        · simpa [Fin.sum_univ_four, a, abs_sub_comm] using hy.2.2.2.1
      have hymem := (imo1966_p5_assumed y a ha).1 hyeq
      simpa [solution_set, solution_set_generalized, x] using hymem
