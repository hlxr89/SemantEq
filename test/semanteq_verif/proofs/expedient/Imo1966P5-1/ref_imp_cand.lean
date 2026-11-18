import Mathlib

set_option maxHeartbeats 5000000

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
  dsimp only
  let A : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have hA : Function.Injective A := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all [A, ne_comm]
  have hmono {i j : Fin 4} (hij : A i < A j) : order A i < order A j := by
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
  have hrank (k : Fin 4) : order A (nth_smallest_index hA k) = k := by
    exact Fintype.rightInverse_bijInv (bijective_order hA) k
  have hlo_le (i : Fin 4) : nth_smallest hA ⟨0, by decide⟩ ≤ A i := by
    by_contra h
    have hv : A i < A (nth_smallest_index hA ⟨0, by decide⟩) := by
      simpa [nth_smallest] using (lt_of_not_ge h)
    have hh := hmono hv
    rw [hrank] at hh
    exact (Fin.not_lt_zero _ hh)
  have hle_hi (i : Fin 4) : A i ≤ nth_smallest hA ⟨3, by decide⟩ := by
    by_contra h
    have hv : A (nth_smallest_index hA ⟨3, by decide⟩) < A i := by
      simpa [nth_smallest] using (lt_of_not_ge h)
    have hh := hmono hv
    rw [hrank] at hh
    have hv := (order A i).isLt
    change 3 < (order A i).val at hh
    omega
  have hlo : nth_smallest hA ⟨0, by decide⟩ =
      min (A 0) (min (A 1) (min (A 2) (A 3))) := by
    apply le_antisymm
    · simp only [le_min_iff]
      exact ⟨hlo_le 0, hlo_le 1, hlo_le 2, hlo_le 3⟩
    · change min (A 0) (min (A 1) (min (A 2) (A 3))) ≤
        A (nth_smallest_index hA ⟨0, by decide⟩)
      generalize nth_smallest_index hA ⟨0, by decide⟩ = k
      fin_cases k <;> simp
  have hhi : nth_smallest hA ⟨3, by decide⟩ =
      max (A 0) (max (A 1) (max (A 2) (A 3))) := by
    apply le_antisymm
    · change A (nth_smallest_index hA ⟨3, by decide⟩) ≤
        max (A 0) (max (A 1) (max (A 2) (A 3)))
      generalize nth_smallest_index hA ⟨3, by decide⟩ = k
      fin_cases k <;> simp
    · simp only [max_le_iff]
      exact ⟨hle_hi 0, hle_hi 1, hle_hi 2, hle_hi 3⟩
  have hextreme (i : Fin 4) :
      (order A i = ⟨0, by decide⟩ ∨ order A i = ⟨3, by decide⟩) ↔
      (A i = max (A 0) (max (A 1) (max (A 2) (A 3))) ∨
       A i = min (A 0) (min (A 1) (min (A 2) (A 3)))) := by
    constructor
    · rintro (hi | hi)
      · right
        rw [← hlo]
        change A i = A (nth_smallest_index hA ⟨0, by decide⟩)
        congr 1
        apply (bijective_order hA).1
        rw [hi, hrank]
      · left
        rw [← hhi]
        change A i = A (nth_smallest_index hA ⟨3, by decide⟩)
        congr 1
        apply (bijective_order hA).1
        rw [hi, hrank]
    · rintro (hi | hi)
      · right
        rw [← hhi] at hi
        rw [← hrank (⟨3, by decide⟩ : Fin 4)]
        change A i = A (nth_smallest_index hA ⟨3, by decide⟩) at hi
        exact congrArg (order A) (hA hi)
      · left
        rw [← hlo] at hi
        rw [← hrank (⟨0, by decide⟩ : Fin 4)]
        change A i = A (nth_smallest_index hA ⟨0, by decide⟩) at hi
        exact congrArg (order A) (hA hi)
  let y : Fin 4 → ℝ := fun i ↦
    if A i = max (A 0) (max (A 1) (max (A 2) (A 3))) ∨
       A i = min (A 0) (min (A 1) (min (A 2) (A 3)))
    then 1 / (max (A 0) (max (A 1) (max (A 2) (A 3))) -
              min (A 0) (min (A 1) (min (A 2) (A 3))))
    else 0
  have hy : y ∈ solution_set hA := by
    change y = fun i : Fin 4 ↦
      if order A i = ⟨0, by decide⟩ ∨ order A i = ⟨4 - 1, by decide⟩
      then 1 / (nth_smallest hA ⟨4 - 1, by decide⟩ - nth_smallest hA ⟨0, by decide⟩)
      else 0
    funext i
    simp only [y]
    norm_num
    have he := hextreme i
    have hlo' : nth_smallest hA (0 : Fin 4) =
        min (A 0) (min (A 1) (min (A 2) (A 3))) := hlo
    norm_num at he
    simp only [he, hhi, hlo']
  have hyE := (imo1966_p5_assumed y A hA).2 hy
  refine ⟨y, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin.sum_univ_succ, A, add_assoc] using hyE 0
    · simpa [Fin.sum_univ_succ, A, add_assoc] using hyE 1
    · simpa [Fin.sum_univ_succ, A, add_assoc] using hyE 2
    · simpa [Fin.sum_univ_succ, A, add_assoc] using hyE 3
    · simp [y, A]
    · simp [y, A]
    · simp [y, A]
    · simp [y, A]
  · intro z hz
    funext i
    fin_cases i
    · simpa [y, A] using hz.2.2.2.2.1
    · simpa [y, A] using hz.2.2.2.2.2.1
    · simpa [y, A] using hz.2.2.2.2.2.2.1
    · simpa [y, A] using hz.2.2.2.2.2.2.2
