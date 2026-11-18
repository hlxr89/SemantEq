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
set_option maxHeartbeats 2000000 in
theorem imo1966_p5
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  have hne : a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 0 ≠ a 3 ∧
      a 1 ≠ a 2 ∧ a 1 ≠ a 3 ∧ a 2 ≠ a 3 := by
    repeat' apply And.intro
    all_goals exact ha.ne (by decide)
  obtain ⟨y, hy, -⟩ := problem_statement_assumed (a 0) (a 1) (a 2) (a 3) hne
  have hyeq : ∀ q : Fin 4, ∑ r : Fin 4, abs (a q - a r) * y r = 1 := by
    intro q
    fin_cases q
    · simpa [Fin.sum_univ_four] using hy.1
    · simpa [Fin.sum_univ_four] using hy.2.1
    · simpa [Fin.sum_univ_four] using hy.2.2.1
    · simpa [Fin.sum_univ_four] using hy.2.2.2.1
  have huniq : ∀ u v : Fin 4 → ℝ,
      (∀ q : Fin 4, ∑ r : Fin 4, abs (a q - a r) * u r = 1) →
      (∀ q : Fin 4, ∑ r : Fin 4, abs (a q - a r) * v r = 1) → u = v := by
    intro u v hu hv
    let s : Fin 4 → Fin 4 := nth_smallest_index ha
    have hsbij : Function.Bijective s := Fintype.bijective_bijInv (bijective_order ha)
    let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective s hsbij
    have hs (k : Fin 4) : order a (s k) = k :=
      Fintype.rightInverse_bijInv (bijective_order ha) k
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
    have hslt : ∀ p q : Fin 4, p < q → a (s p) < a (s q) := by
      intro p q hpq
      have hnepq : a (s p) ≠ a (s q) := by
        apply ha.ne
        apply hsbij.1.ne
        exact ne_of_lt hpq
      rcases lt_or_gt_of_ne hnepq with h | h
      · exact h
      · have ho := hmono (s q) (s p) h
        rw [hs q, hs p] at ho
        exact False.elim ((not_lt_of_ge (le_of_lt hpq)) ho)
    have h01 := hslt 0 1 (by decide)
    have h12 := hslt 1 2 (by decide)
    have h23 := hslt 2 3 (by decide)
    have h02 : a (s 0) < a (s 2) := lt_trans h01 h12
    have h13 : a (s 1) < a (s 3) := lt_trans h12 h23
    have h03 : a (s 0) < a (s 3) := lt_trans h02 h23
    have hu' (k : Fin 4) :
        ∑ l : Fin 4, abs (a (s k) - a (s l)) * u (s l) = 1 := by
      calc
        _ = ∑ r : Fin 4, abs (a (s k) - a r) * u r :=
          Fintype.sum_bijective s hsbij _ _ (fun _ ↦ rfl)
        _ = 1 := hu (s k)
    have hv' (k : Fin 4) :
        ∑ l : Fin 4, abs (a (s k) - a (s l)) * v (s l) = 1 := by
      calc
        _ = ∑ r : Fin 4, abs (a (s k) - a r) * v r :=
          Fintype.sum_bijective s hsbij _ _ (fun _ ↦ rfl)
        _ = 1 := hv (s k)
    have hu0 := hu' 0
    have hu1 := hu' 1
    have hu2 := hu' 2
    have hu3 := hu' 3
    have hv0 := hv' 0
    have hv1 := hv' 1
    have hv2 := hv' 2
    have hv3 := hv' 3
    simp only [Fin.sum_univ_four] at hu0 hu1 hu2 hu3 hv0 hv1 hv2 hv3
    simp [abs_of_pos, abs_of_neg, h01, h12, h23, h02, h13, h03] at hu0 hu1 hu2 hu3 hv0 hv1 hv2 hv3
    let p := a (s 1) - a (s 0)
    let q := a (s 2) - a (s 1)
    let r := a (s 3) - a (s 2)
    let t := p + q + r
    have hp : 0 < p := by dsimp [p]; linarith
    have hq : 0 < q := by dsimp [q]; linarith
    have hr : 0 < r := by dsimp [r]; linarith
    have h0 : u (s 0) = v (s 0) := by
      have hh : (-4 * p * q * r * t) * (u (s 0) - v (s 0)) = 0 := by
        dsimp [p, q, r, t]
        linear_combination
          2 * (a (s 2) - a (s 1)) * (a (s 3) - a (s 2)) * (a (s 3) - a (s 1)) * (hu0 - hv0) -
          2 * (a (s 2) - a (s 1)) * (a (s 3) - a (s 2)) * (a (s 3) - a (s 0)) * (hu1 - hv1) -
          2 * (a (s 1) - a (s 0)) * (a (s 2) - a (s 1)) * (a (s 3) - a (s 2)) * (hu3 - hv3)
      have ht : 0 < t := by dsimp [t]; linarith
      have hc : -4 * p * q * r * t ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hc)
    have h1 : u (s 1) = v (s 1) := by
      have hh : (-4 * p * q * r * t) * (u (s 1) - v (s 1)) = 0 := by
        dsimp [p, q, r, t]
        linear_combination
          -2 * (a (s 2) - a (s 1)) * (a (s 3) - a (s 2)) * (a (s 3) - a (s 0)) * (hu0 - hv0) +
          2 * (a (s 3) - a (s 2)) * (a (s 3) - a (s 0)) * (a (s 2) - a (s 0)) * (hu1 - hv1) -
          2 * (a (s 1) - a (s 0)) * (a (s 3) - a (s 2)) * (a (s 3) - a (s 0)) * (hu2 - hv2)
      have ht : 0 < t := by dsimp [t]; linarith
      have hc : -4 * p * q * r * t ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hc)
    have h2 : u (s 2) = v (s 2) := by
      have hh : (-4 * p * q * r * t) * (u (s 2) - v (s 2)) = 0 := by
        dsimp [p, q, r, t]
        linear_combination
          -2 * (a (s 1) - a (s 0)) * (a (s 3) - a (s 2)) * (a (s 3) - a (s 0)) * (hu1 - hv1) +
          2 * (a (s 1) - a (s 0)) * (a (s 3) - a (s 0)) * (a (s 3) - a (s 1)) * (hu2 - hv2) -
          2 * (a (s 1) - a (s 0)) * (a (s 2) - a (s 1)) * (a (s 3) - a (s 0)) * (hu3 - hv3)
      have ht : 0 < t := by dsimp [t]; linarith
      have hc : -4 * p * q * r * t ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hc)
    have h3 : u (s 3) = v (s 3) := by
      have hh : (-4 * p * q * r * t) * (u (s 3) - v (s 3)) = 0 := by
        dsimp [p, q, r, t]
        linear_combination
          -2 * (a (s 1) - a (s 0)) * (a (s 2) - a (s 1)) * (a (s 3) - a (s 2)) * (hu0 - hv0) -
          2 * (a (s 1) - a (s 0)) * (a (s 2) - a (s 1)) * (a (s 3) - a (s 0)) * (hu2 - hv2) +
          2 * (a (s 1) - a (s 0)) * (a (s 2) - a (s 1)) * (a (s 2) - a (s 0)) * (hu3 - hv3)
      have ht : 0 < t := by dsimp [t]; linarith
      have hc : -4 * p * q * r * t ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hc)
    funext k
    obtain ⟨l, rfl⟩ := hsbij.2 k
    fin_cases l <;> assumption
  let z : Fin 4 → ℝ := fun i ↦
    if order a i = ⟨0, by lia⟩ ∨ order a i = ⟨4 - 1, by lia⟩
    then 1 / (nth_smallest ha ⟨4 - 1, by lia⟩ - nth_smallest ha ⟨0, by lia⟩)
    else 0
  have hzmem : z ∈ solution_set ha := by rfl
  have hzeq : ∀ q : Fin 4, ∑ r : Fin 4, abs (a q - a r) * z r = 1 := by
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
    have hile : ∀ q : Fin 4, a i ≤ a q := by
      simpa [order, raw_order] using hi
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
    have hjge : ∀ q : Fin 4, a q ≤ a j := by
      intro q
      by_contra hn
      have hltorder := hmono j q (lt_of_not_ge hn)
      rw [hj] at hltorder
      change 3 < (order a q).val at hltorder
      have hq := (order a q).isLt
      omega
    have hz_i : z i = 1 / (a j - a i) := by
      dsimp [z]
      rw [if_pos]
      · rfl
      · exact Or.inl (by simpa using hi)
    have hz_j : z j = 1 / (a j - a i) := by
      dsimp [z]
      rw [if_pos]
      · rfl
      · exact Or.inr (by simpa using hj)
    have hz_other : ∀ k : Fin 4, k ≠ i → k ≠ j → z k = 0 := by
      intro k hki hkj
      have hk0 : order a k ≠ ⟨0, by omega⟩ := by
        intro heq
        exact hki ((bijective_order ha).1 (heq.trans hi.symm))
      have hk3 : order a k ≠ ⟨3, by omega⟩ := by
        intro heq
        exact hkj ((bijective_order ha).1 (heq.trans hj.symm))
      dsimp [z]
      rw [if_neg]
      intro hor
      rcases hor with hor | hor
      · exact hk0 (by simpa using hor)
      · exact hk3 (by simpa using hor)
    intro q
    classical
    let f : Fin 4 → ℝ := fun r ↦ abs (a q - a r) * z r
    have hs : ∑ r ∈ Finset.univ.erase i, f r = f j := by
      apply Finset.sum_eq_single j
      · intro b hb hbj
        have hbi : b ≠ i := (Finset.mem_erase.mp hb).1
        simp [f, hz_other b hbi hbj]
      · intro hjnot
        exact False.elim (hjnot (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩))
    change ∑ r : Fin 4, f r = 1
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i), hs]
    simp only [f, hz_i, hz_j]
    rw [abs_of_nonneg (sub_nonneg.mpr (hile q))]
    rw [abs_of_nonpos (sub_nonpos.mpr (hjge q))]
    have hpos : 0 < a j - a i := sub_pos.mpr (lt_of_le_of_ne (hile j) (ha.ne hij))
    field_simp [ne_of_gt hpos]
    ring
  have hyz : y = z := huniq y z hyeq hzeq
  constructor
  · intro hx
    have : x = z := (huniq x z hx hzeq)
    simpa [this] using hzmem
  · intro hx
    have : x = z := by
      simpa [solution_set, solution_set_generalized, z] using hx
    simpa [this] using hzeq
