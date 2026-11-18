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
  intro a₁ a₂ a₃ a₄ hpair
  classical
  let a : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have ha : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  let lo : Fin 4 := nth_smallest_index ha 0
  let hi : Fin 4 := nth_smallest_index ha 3
  let d : ℝ := a hi - a lo
  let f : Fin 4 → ℝ := fun i ↦ if i = lo ∨ i = hi then 1 / d else 0
  have hord (k : Fin 4) : order a (nth_smallest_index ha k) = k :=
    Fintype.rightInverse_bijInv (bijective_order ha) k
  have hlo_ord : order a lo = 0 := by simpa [lo] using hord 0
  have hhi_ord : order a hi = 3 := by simpa [hi] using hord 3
  have hlohi : lo ≠ hi := by
    intro h
    rw [h] at hlo_ord
    exact (by decide : (0 : Fin 4) ≠ 3) (hlo_ord.symm.trans hhi_ord)
  have hlo (i : Fin 4) : a lo ≤ a i := by
    apply le_of_not_gt
    intro h
    have hz : raw_order a lo = 0 := congrArg Fin.val hlo_ord
    have he : ({j | a j < a lo} : Finset (Fin 4)) = ∅ := Finset.card_eq_zero.mp hz
    have hm : i ∈ ({j | a j < a lo} : Finset (Fin 4)) := by simp [h]
    rw [he] at hm
    simp at hm
  have horder_lt {i j : Fin 4} (h : a i < a j) : order a i < order a j := by
    simp only [order, raw_order, Fin.mk_lt_mk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_exists_cons_subset]
    use i
    constructor
    · simp
      rw [Finset.insert_subset_iff]
      exact ⟨by simpa, fun k hk => by simp at hk ⊢; exact lt_trans hk h⟩
    · simp
  have hhi (i : Fin 4) : a i ≤ a hi := by
    apply le_of_not_gt
    intro h
    have hh := horder_lt h
    rw [hhi_ord] at hh
    omega
  have hM : max (max a₁ a₂) (max a₃ a₄) = a hi := by
    apply le_antisymm
    · simp only [max_le_iff]
      simpa [a] using And.intro (And.intro (hhi 0) (hhi 1)) (And.intro (hhi 2) (hhi 3))
    · have hcoord (i : Fin 4) : a i ≤ max (max a₁ a₂) (max a₃ a₄) := by
        fin_cases i <;> simp [a]
      exact hcoord hi
  have hm : min (min a₁ a₂) (min a₃ a₄) = a lo := by
    apply le_antisymm
    · have hcoord (i : Fin 4) : min (min a₁ a₂) (min a₃ a₄) ≤ a i := by
        fin_cases i <;> simp [a]
      exact hcoord lo
    · simp only [le_min_iff]
      simpa [a] using And.intro (And.intro (hlo 0) (hlo 1)) (And.intro (hlo 2) (hlo 3))
  have horder_inj := (bijective_order ha).injective
  have hf (i : Fin 4) :
      f i = if order a i = 0 ∨ order a i = 3 then 1 / d else 0 := by
    dsimp [f]
    have h0 : order a i = 0 ↔ i = lo := by
      constructor
      · intro h; apply horder_inj; simpa [h, hlo_ord]
      · rintro rfl; exact hlo_ord
    have h3 : order a i = 3 ↔ i = hi := by
      constructor
      · intro h; apply horder_inj; simpa [h, hhi_ord]
      · rintro rfl; exact hhi_ord
    simp only [h0, h3]
  have fmem : f ∈ solution_set ha := by
    apply Set.mem_singleton_iff.mpr
    funext i
    rw [hf]
    change (if order a i = 0 ∨ order a i = 3 then 1 / d else 0) =
      if order a i = ⟨0, by omega⟩ ∨ order a i = ⟨4 - 1, by omega⟩
      then 1 / (nth_smallest ha ⟨4 - 1, by omega⟩ - nth_smallest ha ⟨0, by omega⟩) else 0
    simp [nth_smallest, lo, hi, d]
  have fsum := (imo1966_p5_assumed f a ha).2 fmem
  have fexplicit :
      (abs (a₁ - a₂) * f 1 + abs (a₁ - a₃) * f 2 + abs (a₁ - a₄) * f 3 = 1) ∧
      (abs (a₂ - a₁) * f 0 + abs (a₂ - a₃) * f 2 + abs (a₂ - a₄) * f 3 = 1) ∧
      (abs (a₃ - a₁) * f 0 + abs (a₃ - a₂) * f 1 + abs (a₃ - a₄) * f 3 = 1) ∧
      (abs (a₄ - a₁) * f 0 + abs (a₄ - a₂) * f 1 + abs (a₄ - a₃) * f 2 = 1) := by
    constructor
    · simpa [a, Fin.sum_univ_four] using fsum 0
    constructor
    · simpa [a, Fin.sum_univ_four, add_assoc] using fsum 1
    constructor
    · simpa [a, Fin.sum_univ_four, add_assoc] using fsum 2
    · simpa [a, Fin.sum_univ_four, add_assoc] using fsum 3
  refine ⟨f, ?_, ?_⟩
  · refine ⟨fexplicit.1, fexplicit.2.1, fexplicit.2.2.1, fexplicit.2.2.2, ?_⟩
    refine ⟨lo, hi, hlohi, ?_, ?_, ?_⟩
    · simp [f, d, hM, hm]
    · simp [f, d, hM, hm, hlohi.symm]
    · intro k hk
      simp [f, hk.1, hk.2]
  · intro y hy
    apply (Set.mem_singleton_iff.mp ((imo1966_p5_assumed y a ha).1 ?_)).trans
      (Set.mem_singleton_iff.mp fmem).symm
    intro i
    fin_cases i
    · simpa [a, Fin.sum_univ_four] using hy.1
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.2.1
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.2.2.1
    · simpa [a, Fin.sum_univ_four, add_assoc] using hy.2.2.2.1
