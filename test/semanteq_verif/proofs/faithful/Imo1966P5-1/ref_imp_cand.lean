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
theorem problem_statement (a₁ a₂ a₃ a₄ : ℝ) 
  (h_distinct : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄ ∧ a₃ ≠ a₄) :
  let M := max a₁ (max a₂ (max a₃ a₄))
  let m := min a₁ (min a₂ (min a₃ a₄))
  ∃! (x : Fin 4 → ℝ), 
    |a₁ - a₂| * x ⟨1, by decide⟩ + |a₁ - a₃| * x ⟨2, by decide⟩ + |a₁ - a₄| * x ⟨3, by decide⟩ = 1 ∧
    |a₂ - a₁| * x ⟨0, by decide⟩ + |a₂ - a₃| * x ⟨2, by decide⟩ + |a₂ - a₄| * x ⟨3, by decide⟩ = 1 ∧
    |a₃ - a₁| * x ⟨0, by decide⟩ + |a₃ - a₂| * x ⟨1, by decide⟩ + |a₃ - a₄| * x ⟨3, by decide⟩ = 1 ∧
    |a₄ - a₁| * x ⟨0, by decide⟩ + |a₄ - a₂| * x ⟨1, by decide⟩ + |a₄ - a₃| * x ⟨2, by decide⟩ = 1 ∧
    (x ⟨0, by decide⟩ = (if a₁ = M ∨ a₁ = m then 1 / (M - m) else 0)) ∧
    (x ⟨1, by decide⟩ = (if a₂ = M ∨ a₂ = m then 1 / (M - m) else 0)) ∧
    (x ⟨2, by decide⟩ = (if a₃ = M ∨ a₃ = m then 1 / (M - m) else 0)) ∧
    (x ⟨3, by decide⟩ = (if a₄ = M ∨ a₄ = m then 1 / (M - m) else 0)) := by
  dsimp
  let a : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have ha : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  let s : Fin 4 → ℝ := fun i ↦
    if order a i = (0 : Fin 4) ∨ order a i = (3 : Fin 4)
    then 1 / (nth_smallest ha 3 - nth_smallest ha 0) else 0
  have hs_mem : s ∈ solution_set ha := by
    rfl
  have hs_eqs := (imo1966_p5_assumed s a ha).2 hs_mem
  have hzero : ∀ i, order a i = (0 : Fin 4) ↔ ∀ j, a i ≤ a j := by
    intro i
    simp [order, raw_order, Fin.ext_iff]
  have hthree : ∀ i, order a i = (3 : Fin 4) ↔ ∀ j, a j ≤ a i := by
    intro i
    simp only [order, Fin.ext_iff, raw_order]
    let t : Finset (Fin 4) := {j | a j < a i}
    have ht : t ⊆ Finset.univ.erase i := by
      rw [Finset.subset_erase]
      exact ⟨Finset.subset_univ _, by simp [t]⟩
    have herase : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
    constructor
    · intro hc j
      have heq : t = Finset.univ.erase i :=
        Finset.eq_of_subset_of_card_le ht (by simpa [herase, t] using hc.ge)
      by_cases hji : j = i
      · simp [hji]
      · have : j ∈ t := by rw [heq]; simp [hji]
        exact (Finset.mem_filter.1 this).2.le
    · intro hall
      have heq : t = Finset.univ.erase i := by
        ext j
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase]
        constructor
        · intro hlt
          exact ⟨fun h ↦ by simpa [h] using hlt, trivial⟩
        · rintro ⟨hji, -⟩
          exact lt_of_le_of_ne (hall j) (fun h ↦ hji (ha h))
      rw [show Finset.card {j | a j < a i} = t.card by rfl, heq, herase]
      norm_num
  have hrank (k : Fin 4) : order a (nth_smallest_index ha k) = k :=
    Fintype.rightInverse_bijInv (bijective_order ha) k
  have hnth0 : nth_smallest ha 0 = min a₁ (min a₂ (min a₃ a₄)) := by
    have hall := (hzero (nth_smallest_index ha 0)).1 (hrank 0)
    apply le_antisymm
    · simp only [nth_smallest, Function.comp_apply, le_min_iff]
      exact ⟨hall 0, hall 1, hall 2, hall 3⟩
    · simp only [nth_smallest, Function.comp_apply]
      generalize hk : nth_smallest_index ha 0 = k
      fin_cases k <;> simp [a] at hk ⊢
  have hnth3 : nth_smallest ha 3 = max a₁ (max a₂ (max a₃ a₄)) := by
    have hall := (hthree (nth_smallest_index ha 3)).1 (hrank 3)
    apply le_antisymm
    · simp only [nth_smallest, Function.comp_apply]
      generalize hk : nth_smallest_index ha 3 = k
      fin_cases k <;> simp [a] at hk ⊢
    · simp only [nth_smallest, Function.comp_apply, max_le_iff]
      exact ⟨hall 0, hall 1, hall 2, hall 3⟩
  have hextreme (i : Fin 4) :
      (order a i = (0 : Fin 4) ∨ order a i = (3 : Fin 4)) ↔
      (a i = max a₁ (max a₂ (max a₃ a₄)) ∨
       a i = min a₁ (min a₂ (min a₃ a₄))) := by
    rw [or_comm]
    constructor
    · rintro (hmax | hmin)
      · left
        have hall := (hthree i).1 hmax
        apply le_antisymm
        · fin_cases i <;> simp [a]
        · simp only [max_le_iff]
          exact ⟨hall 0, hall 1, hall 2, hall 3⟩
      · right
        have hall := (hzero i).1 hmin
        apply le_antisymm
        · simp only [le_min_iff]
          exact ⟨hall 0, hall 1, hall 2, hall 3⟩
        · fin_cases i <;> simp [a]
    · rintro (hmax | hmin)
      · left
        apply (hthree i).2
        intro j
        rw [hmax]
        fin_cases j <;> simp [a]
      · right
        apply (hzero i).2
        intro j
        rw [hmin]
        fin_cases j <;> simp [a]
  have hs_formula (i : Fin 4) : s i =
      if a i = max a₁ (max a₂ (max a₃ a₄)) ∨
          a i = min a₁ (min a₂ (min a₃ a₄))
      then 1 / (max a₁ (max a₂ (max a₃ a₄)) -
        min a₁ (min a₂ (min a₃ a₄))) else 0 := by
    simp only [s, hnth0, hnth3]
    rw [if_congr (hextreme i) rfl rfl]
  refine ⟨s, ?_, ?_⟩
  · constructor
    · simpa [a, Fin.sum_univ_four, add_assoc] using hs_eqs 0
    constructor
    · simpa [a, Fin.sum_univ_four, add_assoc] using hs_eqs 1
    constructor
    · simpa [a, Fin.sum_univ_four, add_assoc] using hs_eqs 2
    constructor
    · simpa [a, Fin.sum_univ_four, add_assoc] using hs_eqs 3
    exact ⟨by simpa [a] using hs_formula 0,
      by simpa [a] using hs_formula 1,
      by simpa [a] using hs_formula 2,
      by simpa [a] using hs_formula 3⟩
  · intro y hy
    apply (Set.mem_singleton_iff.mp ((imo1966_p5_assumed y a ha).1 ?_))
    intro i
    fin_cases i
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.1
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.2.1
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.2.2.1
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.2.2.2.1
