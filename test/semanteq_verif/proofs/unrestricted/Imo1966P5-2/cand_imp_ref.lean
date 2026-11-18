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
theorem problem_statement_assumed :
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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1966_p5
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  classical
  let lo : Fin 4 := nth_smallest_index ha 0
  let hi : Fin 4 := nth_smallest_index ha 3
  let d : ℝ := a hi - a lo
  let f : Fin 4 → ℝ := fun i ↦ if i = lo ∨ i = hi then 1 / d else 0
  have hord (k : Fin 4) : order a (nth_smallest_index ha k) = k := by
    exact Fintype.rightInverse_bijInv (bijective_order ha) k
  have hlo_ord : order a lo = 0 := by simpa [lo] using hord 0
  have hhi_ord : order a hi = 3 := by simpa [hi] using hord 3
  have hlohi : lo ≠ hi := by
    intro h
    rw [h] at hlo_ord
    have : (0 : Fin 4) = 3 := hlo_ord.symm.trans hhi_ord
    exact (by decide : (0 : Fin 4) ≠ 3) this
  have hlo (i : Fin 4) : a lo ≤ a i := by
    apply le_of_not_gt
    intro h
    have hz : raw_order a lo = 0 := congrArg Fin.val hlo_ord
    simp only [order] at hz
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
      constructor
      · simpa using h
      · intro k hk
        simp at hk ⊢
        exact lt_trans hk h
    · simp
  have hhi (i : Fin 4) : a i ≤ a hi := by
    apply le_of_not_gt
    intro h
    have hh := horder_lt h
    rw [hhi_ord] at hh
    omega
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (lt_of_le_of_ne (hlo hi) (ha.ne hlohi))
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
  have feq (i : Fin 4) : ∑ j : Fin 4, abs (a i - a j) * f j = 1 := by
    have hs : (∑ j : Fin 4, abs (a i - a j) * f j) =
        abs (a i - a lo) * (1 / d) + abs (a i - a hi) * (1 / d) := by
      simp_rw [show ∀ j, f j = if j = lo ∨ j = hi then 1 / d else 0 from fun j => rfl]
      rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (i := lo) (by simp)]
      rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ \ {lo}) (i := hi) (by simp [hlohi.symm])]
      have hsum : (∑ j ∈ (Finset.univ \ {lo}) \ {hi},
          abs (a i - a j) * (if j = lo ∨ j = hi then 1 / d else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
        simp [hj.1, hj.2]
      rw [hsum]
      simp [hlohi.symm]
    rw [hs, abs_of_nonneg (sub_nonneg.mpr (hlo i)), abs_of_nonpos (sub_nonpos.mpr (hhi i))]
    field_simp
    linarith
  have unique_eq {z : Fin 4 → ℝ}
      (hz : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * z j = 1) : z = f := by
    let p : Fin 4 → Fin 4 := nth_smallest_index ha
    have hp : Function.Bijective p := Fintype.bijective_bijInv (bijective_order ha)
    have hpord (k : Fin 4) : order a (p k) = k := Fintype.rightInverse_bijInv (bijective_order ha) k
    have hpa {k l : Fin 4} (hkl : k < l) : a (p k) < a (p l) := by
      have hne : p k ≠ p l := fun h => (ne_of_lt hkl) (hp.injective h)
      rcases lt_or_gt_of_ne (ha.ne hne) with h | h
      · exact h
      · have := horder_lt h
        rw [hpord, hpord] at this
        exact (not_lt_of_ge hkl.le this).elim
    have h01 : a (p 0) < a (p 1) := hpa (by decide)
    have h12 : a (p 1) < a (p 2) := hpa (by decide)
    have h23 : a (p 2) < a (p 3) := hpa (by decide)
    have h02 : a (p 0) < a (p 2) := h01.trans h12
    have h13 : a (p 1) < a (p 3) := h12.trans h23
    have h03 : a (p 0) < a (p 3) := h02.trans h23
    let e := Equiv.ofBijective p hp
    have e0 := hz (p 0)
    have e1 := hz (p 1)
    have e2 := hz (p 2)
    have e3 := hz (p 3)
    rw [← e.sum_comp] at e0 e1 e2 e3
    simp [e, Fin.sum_univ_four, abs_of_nonneg, abs_of_nonpos,
      h01.le, h12.le, h23.le, h02.le, h13.le, h03.le] at e0 e1 e2 e3
    have r0 : z (p 0) = z (p 1) + z (p 2) + z (p 3) := by
      have hm : (a (p 1) - a (p 0)) *
          (z (p 0) - z (p 1) - z (p 2) - z (p 3)) = 0 := by nlinarith [e0, e1]
      have := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h01.ne')
      linarith
    have r1 : z (p 0) + z (p 1) = z (p 2) + z (p 3) := by
      have hm : (a (p 2) - a (p 1)) *
          (z (p 0) + z (p 1) - z (p 2) - z (p 3)) = 0 := by nlinarith [e1, e2]
      have := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h12.ne')
      linarith
    have r2 : z (p 0) + z (p 1) + z (p 2) = z (p 3) := by
      have hm : (a (p 3) - a (p 2)) *
          (z (p 0) + z (p 1) + z (p 2) - z (p 3)) = 0 := by nlinarith [e2, e3]
      have := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h23.ne')
      linarith
    have z1 : z (p 1) = 0 := by linarith
    have z2 : z (p 2) = 0 := by linarith
    have ze : z (p 0) = z (p 3) := by linarith
    have z3 : z (p 3) = 1 / (a (p 3) - a (p 0)) := by
      apply (eq_div_iff (sub_ne_zero.mpr h03.ne')).2
      rw [z1, z2] at e0
      norm_num at e0
      nlinarith
    have z0 : z (p 0) = 1 / (a (p 3) - a (p 0)) := ze.trans z3
    funext i
    have hpi : p (order a i) = i := Fintype.leftInverse_bijInv (bijective_order ha) i
    generalize hk : order a i = k
    have hi' : i = p k := by rw [← hpi, hk]
    rw [hi']
    have hp10 : p 1 ≠ p 0 := hp.injective.ne (by decide)
    have hp13 : p 1 ≠ p 3 := hp.injective.ne (by decide)
    have hp20 : p 2 ≠ p 0 := hp.injective.ne (by decide)
    have hp23 : p 2 ≠ p 3 := hp.injective.ne (by decide)
    fin_cases k <;> simp [f, lo, hi, d, p, z0, z1, z2, z3, hp10, hp13, hp20, hp23]
  constructor
  · intro hx
    rw [unique_eq hx]
    exact fmem
  · intro hx
    have : x = f := (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp fmem).symm
    simpa [this] using feq
