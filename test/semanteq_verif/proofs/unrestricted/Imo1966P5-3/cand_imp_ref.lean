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
  : Fin n → Fin n := Fintype.bijInv (bijective_order ha)
noncomputable def nth_smallest {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Fin n → ℝ := a ∘ (nth_smallest_index ha)
noncomputable def solution_set_generalized {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : Function.Injective a) : Set ((Fin n → ℝ)) := {
    fun i : Fin n ↦
      if order a i = ⟨0, by lia⟩ ∨ order a i = ⟨n - 1, by lia⟩
      then 1 / (nth_smallest ha ⟨n - 1, by lia⟩ - nth_smallest ha ⟨0, by lia⟩)
      else 0 }
noncomputable abbrev solution_set {a : Fin 4 → ℝ} (ha : Function.Injective a) : Set ((Fin 4 → ℝ)) :=
  solution_set_generalized (by norm_num : 2 ≤ 4) ha


def max_of_four (a₁ a₂ a₃ a₄ : ℝ) : ℝ := max a₁ (max a₂ (max a₃ a₄))
def min_of_four (a₁ a₂ a₃ a₄ : ℝ) : ℝ := min a₁ (min a₂ (min a₃ a₄))

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed 
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
       else False)) := sorry

lemma fin4_mk_two (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := Fin.ext rfl
lemma fin4_mk_three (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := Fin.ext rfl

lemma solution_set_of_sorted (a x : Fin 4 → ℝ) (ha : Function.Injective a)
    (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) :
    x ∈ solution_set ha ↔ x = ![1/(a 3-a 0), 0, 0, 1/(a 3-a 0)] := by
  simp only [solution_set, solution_set_generalized, Set.mem_singleton_iff]
  have hord : order a = id := by
    have hr0 : raw_order a 0 = 0 := by
      unfold raw_order
      rw [Finset.card_filter]
      change (∑ j : Fin 4, if a j < a 0 then 1 else 0) = 0
      rw [Fin.sum_univ_four]
      split_ifs <;> norm_num <;> linarith
    have hr1 : raw_order a 1 = 1 := by
      unfold raw_order
      rw [Finset.card_filter]
      change (∑ j : Fin 4, if a j < a 1 then 1 else 0) = 1
      rw [Fin.sum_univ_four]
      split_ifs <;> norm_num <;> linarith
    have hr2 : raw_order a 2 = 2 := by
      unfold raw_order
      rw [Finset.card_filter]
      change (∑ j : Fin 4, if a j < a 2 then 1 else 0) = 2
      rw [Fin.sum_univ_four]
      split_ifs <;> norm_num <;> linarith
    have hr3 : raw_order a 3 = 3 := by
      unfold raw_order
      rw [Finset.card_filter]
      change (∑ j : Fin 4, if a j < a 3 then 1 else 0) = 3
      rw [Fin.sum_univ_four]
      split_ifs <;> norm_num <;> linarith
    funext i
    fin_cases i
    · exact Fin.ext hr0
    · exact Fin.ext hr1
    · exact Fin.ext hr2
    · exact Fin.ext hr3
  have hnth : nth_smallest ha = a := by
    funext i
    change a (nth_smallest_index ha i) = a i
    congr 1
    unfold nth_smallest_index
    exact (by simpa [hord] using Fintype.rightInverse_bijInv (bijective_order ha) i)
  rw [hnth]
  constructor <;> intro hx
  · rw [hx]
    funext i
    rw [hord]
    fin_cases i <;> simp
  · rw [hx]
    funext i
    rw [hord]
    fin_cases i <;> simp

lemma equations_of_sorted (a x : Fin 4 → ℝ)
    (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3)
    (h : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1) :
    x 0 = 1/(a 3-a 0) ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 1/(a 3-a 0) := by
  have h02 := lt_trans h01 h12
  have h13 := lt_trans h12 h23
  have h03 := lt_trans h02 h23
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have hs : (Fin.succ 2 : Fin 4) = 3 := by decide
  norm_num [Fin.sum_univ_succ, hs, abs_of_pos, abs_of_neg, h01, h12, h23, h02, h13, h03] at h0 h1 h2 h3
  have hd : a 3 - a 0 ≠ 0 := ne_of_gt (sub_pos.mpr h03)
  have hx1p : 2 * (a 1 - a 0) * (a 2 - a 1) * x 1 = 0 := by
    linear_combination (a 1 - a 0) * (h2 - h1) - (a 2 - a 1) * (h1 - h0)
  have hx1 : x 1 = 0 := by
    exact (mul_eq_zero.mp hx1p).resolve_left
      (ne_of_gt (mul_pos (mul_pos (by norm_num) (sub_pos.mpr h01)) (sub_pos.mpr h12)))
  have hx2p : 2 * (a 2 - a 1) * (a 3 - a 2) * x 2 = 0 := by
    linear_combination (a 2 - a 1) * (h3 - h2) - (a 3 - a 2) * (h2 - h1)
  have hx2 : x 2 = 0 := by
    exact (mul_eq_zero.mp hx2p).resolve_left
      (ne_of_gt (mul_pos (mul_pos (by norm_num) (sub_pos.mpr h12)) (sub_pos.mpr h23)))
  constructor
  · field_simp
    rw [hx1, hx2] at h3
    norm_num at h3
    simpa [mul_comm] using h3
  constructor
  · exact hx1
  constructor
  · exact hx2
  · field_simp
    rw [hx1, hx2] at h0
    norm_num at h0
    simpa [mul_comm] using h0

lemma raw_order_comp_equiv {n : ℕ} (a : Fin n → ℝ) (e : Fin n ≃ Fin n) (i : Fin n) :
    raw_order (a ∘ e) i = raw_order a (e i) := by
  unfold raw_order
  apply Finset.card_bij' (fun j _ => e j) (fun j _ => e.symm j)
  · simp
  · simp
  · simp
  · simp

lemma order_comp_equiv {n : ℕ} (a : Fin n → ℝ) (e : Fin n ≃ Fin n) (i : Fin n) :
    order (a ∘ e) i = order a (e i) := by
  apply Fin.ext
  exact raw_order_comp_equiv a e i

lemma nth_smallest_comp_equiv {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
    (e : Fin n ≃ Fin n) :
    nth_smallest (ha.comp e.injective) = nth_smallest ha := by
  funext k
  change a (e (nth_smallest_index (ha.comp e.injective) k)) = a (nth_smallest_index ha k)
  congr 1
  apply (bijective_order ha).1
  rw [← order_comp_equiv a e]
  unfold nth_smallest_index
  rw [Fintype.rightInverse_bijInv (bijective_order (ha.comp e.injective))]
  rw [Fintype.rightInverse_bijInv (bijective_order ha)]

lemma solution_set_comp_equiv {a x : Fin 4 → ℝ} (ha : Function.Injective a)
    (e : Fin 4 ≃ Fin 4) :
    x ∈ solution_set ha ↔ x ∘ e ∈ solution_set (ha.comp e.injective) := by
  simp only [solution_set, solution_set_generalized, Set.mem_singleton_iff]
  rw [nth_smallest_comp_equiv ha e]
  constructor
  · intro hx
    rw [hx]
    funext i
    rw [order_comp_equiv]
    rfl
  · intro hx
    funext j
    have h := congrFun hx (e.symm j)
    simpa [order_comp_equiv] using h

lemma exists_sorted_equiv (a : Fin 4 → ℝ) (ha : Function.Injective a) :
    ∃ e : Fin 4 ≃ Fin 4, a (e 0) < a (e 1) ∧ a (e 1) < a (e 2) ∧ a (e 2) < a (e 3) := by
  let s : Finset ℝ := Finset.univ.image a
  have hs : s.card = 4 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ ha
  let v : Fin 4 ↪o ℝ := s.orderEmbOfFin hs
  have hv : ∀ k : Fin 4, ∃ i : Fin 4, a i = v k := by
    intro k
    have hm := Finset.orderEmbOfFin_mem s hs k
    change v k ∈ Finset.univ.image a at hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  choose f hf using hv
  have hfi : Function.Injective f := by
    intro i j hij
    apply v.injective
    rw [← hf i, ← hf j, hij]
  have hfb : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hfi, rfl⟩
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective f hfb
  refine ⟨e, ?_, ?_, ?_⟩
  · change a (f 0) < a (f 1)
    rw [hf, hf]
    exact v.strictMono (by decide)
  · change a (f 1) < a (f 2)
    rw [hf, hf]
    exact v.strictMono (by decide)
  · change a (f 2) < a (f 3)
    rw [hf, hf]
    exact v.strictMono (by decide)

lemma sorted_iff_solution (a x : Fin 4 → ℝ) (ha : Function.Injective a)
    (h01 : a 0 < a 1) (h12 : a 1 < a 2) (h23 : a 2 < a 3) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1) ↔ x ∈ solution_set ha := by
  rw [solution_set_of_sorted a x ha h01 h12 h23]
  constructor
  · intro h
    have hx := equations_of_sorted a x h01 h12 h23 h
    funext i
    fin_cases i <;> simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  · intro hx
    rw [hx]
    intro i
    have h03 : a 0 < a 3 := lt_trans h01 (lt_trans h12 h23)
    have hd : a 3 - a 0 ≠ 0 := ne_of_gt (sub_pos.mpr h03)
    have hlo : a 0 ≤ a i := by fin_cases i <;> simp [fin4_mk_two, fin4_mk_three] <;> linarith
    have hhi : a i ≤ a 3 := by fin_cases i <;> simp [fin4_mk_two, fin4_mk_three] <;> linarith
    rw [Fin.sum_univ_four]
    simp [fin4_mk_two, fin4_mk_three]
    rw [abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonpos (sub_nonpos.mpr hhi)]
    field_simp
    ring

lemma equations_comp_equiv {a x : Fin 4 → ℝ} (e : Fin 4 ≃ Fin 4) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1) ↔
      ∀ i : Fin 4, ∑ j : Fin 4, abs ((a ∘ e) i - (a ∘ e) j) * (x ∘ e) j = 1 := by
  constructor
  · intro h i
    change (∑ j : Fin 4, abs (a (e i) - a (e j)) * x (e j)) = 1
    calc
      _ = ∑ j : Fin 4, abs (a (e i) - a j) * x j :=
        e.sum_comp (fun j => abs (a (e i) - a j) * x j)
      _ = 1 := h (e i)
  · intro h i
    have hi := h (e.symm i)
    simp only [Function.comp_apply, e.apply_symm_apply] at hi
    change (∑ j : Fin 4, abs (a i - a (e j)) * x (e j)) = 1 at hi
    calc
      _ = ∑ j : Fin 4, abs (a i - a (e j)) * x (e j) :=
        (e.sum_comp (fun j => abs (a i - a j) * x j)).symm
      _ = 1 := hi

lemma imo_core (x a : Fin 4 → ℝ) (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1) ↔ x ∈ solution_set ha := by
  obtain ⟨e, h01, h12, h23⟩ := exists_sorted_equiv a ha
  rw [equations_comp_equiv e, solution_set_comp_equiv ha e]
  exact sorted_iff_solution (a ∘ e) (x ∘ e) (ha.comp e.injective) h01 h12 h23


-- ===== goal statement, PROVED from the antecedent =====
theorem imo1966_p5
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  exact imo_core x a ha

