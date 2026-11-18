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
theorem problem_statement_assumed (a₁ a₂ a₃ a₄ : ℝ) 
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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1966_p5
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  have hmono {i j : Fin 4} (hij : a i < a j) : order a i < order a j := by
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
  have hrank (k : Fin 4) : order a (nth_smallest_index ha k) = k := by
    exact Fintype.rightInverse_bijInv (bijective_order ha) k
  have hlo_le (i : Fin 4) : nth_smallest ha ⟨0, by decide⟩ ≤ a i := by
    by_contra h
    have hh := hmono (lt_of_not_ge h)
    rw [hrank] at hh
    exact (Fin.not_lt_zero _ hh)
  have hle_hi (i : Fin 4) : a i ≤ nth_smallest ha ⟨3, by decide⟩ := by
    by_contra h
    have hh := hmono (lt_of_not_ge h)
    rw [hrank] at hh
    have hv := (order a i).isLt
    change 3 < (order a i).val at hh
    omega
  have hlo : nth_smallest ha ⟨0, by decide⟩ =
      min (a 0) (min (a 1) (min (a 2) (a 3))) := by
    apply le_antisymm
    · simp only [le_min_iff]
      exact ⟨hlo_le 0, hlo_le 1, hlo_le 2, hlo_le 3⟩
    · change min (a 0) (min (a 1) (min (a 2) (a 3))) ≤
        a (nth_smallest_index ha ⟨0, by decide⟩)
      generalize nth_smallest_index ha ⟨0, by decide⟩ = k
      fin_cases k <;> simp
  have hhi : nth_smallest ha ⟨3, by decide⟩ =
      max (a 0) (max (a 1) (max (a 2) (a 3))) := by
    apply le_antisymm
    · change a (nth_smallest_index ha ⟨3, by decide⟩) ≤
        max (a 0) (max (a 1) (max (a 2) (a 3)))
      generalize nth_smallest_index ha ⟨3, by decide⟩ = k
      fin_cases k <;> simp
    · simp only [max_le_iff]
      exact ⟨hle_hi 0, hle_hi 1, hle_hi 2, hle_hi 3⟩
  have hextreme (i : Fin 4) :
      (order a i = ⟨0, by decide⟩ ∨ order a i = ⟨3, by decide⟩) ↔
      (a i = max (a 0) (max (a 1) (max (a 2) (a 3))) ∨
       a i = min (a 0) (min (a 1) (min (a 2) (a 3)))) := by
    constructor
    · rintro (hi | hi)
      · right
        rw [← hlo]
        change a i = a (nth_smallest_index ha ⟨0, by decide⟩)
        congr 1
        apply (bijective_order ha).1
        rw [hi, hrank]
      · left
        rw [← hhi]
        change a i = a (nth_smallest_index ha ⟨3, by decide⟩)
        congr 1
        apply (bijective_order ha).1
        rw [hi, hrank]
    · rintro (hi | hi)
      · right
        rw [← hhi] at hi
        rw [← hrank (⟨3, by decide⟩ : Fin 4)]
        change a i = a (nth_smallest_index ha ⟨3, by decide⟩) at hi
        exact congrArg (order a) (ha hi)
      · left
        rw [← hlo] at hi
        rw [← hrank (⟨0, by decide⟩ : Fin 4)]
        change a i = a (nth_smallest_index ha ⟨0, by decide⟩) at hi
        exact congrArg (order a) (ha hi)
  have hcanonical :
      (fun i : Fin 4 ↦
        if order a i = ⟨0, by decide⟩ ∨ order a i = ⟨4 - 1, by decide⟩
        then 1 / (nth_smallest ha ⟨4 - 1, by decide⟩ - nth_smallest ha ⟨0, by decide⟩)
        else 0) =
      (fun i : Fin 4 ↦
        if a i = max (a 0) (max (a 1) (max (a 2) (a 3))) ∨
           a i = min (a 0) (min (a 1) (min (a 2) (a 3)))
        then 1 / (max (a 0) (max (a 1) (max (a 2) (a 3))) -
                  min (a 0) (min (a 1) (min (a 2) (a 3))))
        else 0) := by
    funext i
    norm_num
    have he := hextreme i
    have hlo' : nth_smallest ha (0 : Fin 4) =
        min (a 0) (min (a 1) (min (a 2) (a 3))) := hlo
    norm_num at he
    simp only [he, hhi, hlo']
  change (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1) ↔
    x = (fun i : Fin 4 ↦
      if order a i = ⟨0, by decide⟩ ∨ order a i = ⟨4 - 1, by decide⟩
      then 1 / (nth_smallest ha ⟨4 - 1, by decide⟩ - nth_smallest ha ⟨0, by decide⟩)
      else 0)
  rw [hcanonical]
  rw [← hcanonical]
  let e : Fin 4 ≃ Fin 4 := {
    toFun := nth_smallest_index ha
    invFun := order a
    left_inv := Fintype.rightInverse_bijInv (bijective_order ha)
    right_inv := Fintype.leftInverse_bijInv (bijective_order ha) }
  have he (k : Fin 4) : order a (e k) = k := e.symm_apply_apply k
  have hae (k : Fin 4) : a (e k) = nth_smallest ha k := rfl
  have hs {k l : Fin 4} (hkl : k < l) : a (e k) < a (e l) := by
    rcases lt_or_gt_of_ne (ha.ne (e.injective.ne (ne_of_lt hkl))) with h | h
    · exact h
    · have hh := hmono h
      rw [he, he] at hh
      exact (not_lt_of_ge (le_of_lt hkl)) hh |>.elim
  have h01 : a (e 0) < a (e 1) := hs (by decide)
  have h02 : a (e 0) < a (e 2) := hs (by decide)
  have h03 : a (e 0) < a (e 3) := hs (by decide)
  have h12 : a (e 1) < a (e 2) := hs (by decide)
  have h13 : a (e 1) < a (e 3) := hs (by decide)
  have h23 : a (e 2) < a (e 3) := hs (by decide)
  constructor
  · intro h
    have h0 := h (e 0)
    have h1 := h (e 1)
    have h2 := h (e 2)
    have h3 := h (e 3)
    rw [← e.sum_comp] at h0 h1 h2 h3
    simp [Fin.sum_univ_succ, abs_of_pos, abs_of_neg, h01, h02, h03,
      h12, h13, h23] at h0 h1 h2 h3
    have hs0 : (a (e 1) - a (e 0)) *
        (x (e 0) - x (e 1) - x (e 2) - x (e 3)) = 0 := by
      nlinarith [h0, h1]
    have hs1 : (a (e 2) - a (e 1)) *
        (x (e 0) + x (e 1) - x (e 2) - x (e 3)) = 0 := by
      nlinarith [h1, h2]
    have hs2 : (a (e 3) - a (e 2)) *
        (x (e 0) + x (e 1) + x (e 2) - x (e 3)) = 0 := by
      nlinarith [h2, h3]
    have hs0' := (mul_eq_zero.mp hs0).resolve_left (ne_of_gt (sub_pos.mpr h01))
    have hs1' := (mul_eq_zero.mp hs1).resolve_left (ne_of_gt (sub_pos.mpr h12))
    have hs2' := (mul_eq_zero.mp hs2).resolve_left (ne_of_gt (sub_pos.mpr h23))
    have hx1 : x (e 1) = 0 := by linarith
    have hx2 : x (e 2) = 0 := by linarith
    have hx03 : x (e 0) = x (e 3) := by linarith
    have hx3 : x (e 3) = 1 / (a (e 3) - a (e 0)) := by
      rw [eq_div_iff (ne_of_gt (sub_pos.mpr h03))]
      nlinarith [h0]
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    fin_cases k
    · simp [he]
      rw [← hae 3, ← hae 0, hx03, hx3]
      simp [one_div]
    · simp [he]
      exact hx1
    · simp [he]
      exact hx2
    · simp [he]
      rw [← hae 3, ← hae 0, hx3]
      simp [one_div]
  · intro hx
    subst x
    intro i
    obtain ⟨k, rfl⟩ := e.surjective i
    rw [← e.sum_comp]
    have hden : nth_smallest ha (3 : Fin 4) - nth_smallest ha (0 : Fin 4) =
        a (e 3) - a (e 0) := by rw [← hae 3, ← hae 0]
    have hne : a (e 3) - a (e 0) ≠ 0 := ne_of_gt (sub_pos.mpr h03)
    fin_cases k <;>
      simp [Fin.sum_univ_succ, he, hden, abs_of_pos, abs_of_neg, h01, h02, h03,
        h12, h13, h23] <;>
      field_simp [hne] <;> nlinarith
