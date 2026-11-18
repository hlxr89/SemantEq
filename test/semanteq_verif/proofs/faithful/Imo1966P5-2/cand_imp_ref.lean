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
  let p : Fin 4 → Fin 4 := nth_smallest_index ha
  have hp (k : Fin 4) : order a (p k) = k :=
    Fintype.rightInverse_bijInv (bijective_order ha) k
  have hp_inj : Function.Injective p := by
    intro i j h
    have := congrArg (order a) h
    simpa [hp i, hp j] using this
  have hp_bij : Function.Bijective p := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hp_inj, rfl⟩
  let ep : Fin 4 ≃ Fin 4 := Equiv.ofBijective p hp_bij
  let b : Fin 4 → ℝ := fun k ↦ a (p k)
  have hord_lt {i j : Fin 4} (hij : a i < a j) : order a i < order a j := by
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
  have hb_lt {k l : Fin 4} (hkl : k < l) : b k < b l := by
    rcases lt_trichotomy (b k) (b l) with h | h | h
    · exact h
    · exact False.elim ((ne_of_lt hkl) (hp_inj (ha h)))
    · have := hord_lt h
      rw [hp k, hp l] at this
      omega
  have hb01 : b 0 < b 1 := hb_lt (by omega)
  have hb12 : b 1 < b 2 := hb_lt (by omega)
  have hb23 : b 2 < b 3 := hb_lt (by omega)
  have hb02 : b 0 < b 2 := lt_trans hb01 hb12
  have hb13 : b 1 < b 3 := lt_trans hb12 hb23
  have hb03 : b 0 < b 3 := lt_trans hb02 hb23
  have hmin (j : Fin 4) : b 0 ≤ a j := by
    by_contra h
    have := hord_lt (lt_of_not_ge h)
    rw [hp 0] at this
    omega
  have hmax (j : Fin 4) : a j ≤ b 3 := by
    by_contra h
    have := hord_lt (lt_of_not_ge h)
    rw [hp 3] at this
    omega
  have hMin : min (min (a 0) (a 1)) (min (a 2) (a 3)) = b 0 := by
    apply le_antisymm
    · have hi : p 0 = 0 ∨ p 0 = 1 ∨ p 0 = 2 ∨ p 0 = 3 := by omega
      rcases hi with hi | hi | hi | hi <;> simp [b, hi]
    · simp only [le_min_iff]
      exact ⟨⟨hmin 0, hmin 1⟩, hmin 2, hmin 3⟩
  have hMax : max (max (a 0) (a 1)) (max (a 2) (a 3)) = b 3 := by
    apply le_antisymm
    · simp only [max_le_iff]
      exact ⟨⟨hmax 0, hmax 1⟩, hmax 2, hmax 3⟩
    · have hi : p 3 = 0 ∨ p 3 = 1 ∨ p 3 = 2 ∨ p 3 = 3 := by omega
      rcases hi with hi | hi | hi | hi <;> simp [b, hi]
  have hne : a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 0 ≠ a 3 ∧
      a 1 ≠ a 2 ∧ a 1 ≠ a 3 ∧ a 2 ≠ a 3 := by
    constructor
    · exact ha.ne (by decide)
    constructor
    · exact ha.ne (by decide)
    constructor
    · exact ha.ne (by decide)
    constructor
    · exact ha.ne (by decide)
    constructor
    · exact ha.ne (by decide)
    · exact ha.ne (by decide)
  obtain ⟨y, hy, _⟩ := problem_statement_assumed (a 0) (a 1) (a 2) (a 3) hne
  have hyeq : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * y j = 1 := by
    intro i
    fin_cases i
    · simpa [Fin.sum_univ_four] using hy.1
    · simpa [Fin.sum_univ_four] using hy.2.1
    · simpa [Fin.sum_univ_four] using hy.2.2.1
    · simpa [Fin.sum_univ_four] using hy.2.2.2.1
  rcases hy.2.2.2.2 with ⟨i, j, hij, hyi, hyj, hyzero⟩
  rw [hMax, hMin] at hyi hyj
  have hyfun : y = fun k ↦ if k = i then 1 / (b 3 - b 0)
      else if k = j then 1 / (b 3 - b 0) else 0 := by
    funext k
    by_cases hki : k = i
    · simp [hki, hyi]
    by_cases hkj : k = j
    · rw [hkj]
      simp
      simpa [one_div] using hyj
    · simp [hki, hkj, hyzero k ⟨hki, hkj⟩]
  have hR : b 3 - b 0 ≠ 0 := by linarith
  have heij := hyeq i
  rw [hyfun] at heij
  have hsum : (∑ k : Fin 4, if k = i then abs (a i - a k) / (b 3 - b 0)
      else if k = j then abs (a i - a k) / (b 3 - b 0) else 0) =
      abs (a i - a i) / (b 3 - b 0) + abs (a i - a j) / (b 3 - b 0) := by
    calc
      _ = ∑ k : Fin 4, ((if k = i then abs (a i - a k) / (b 3 - b 0) else 0) +
          (if k = j then abs (a i - a k) / (b 3 - b 0) else 0)) := by
            apply Finset.sum_congr rfl
            intro k _
            have hji : j ≠ i := Ne.symm hij
            by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hij, hji]
      _ = (∑ k : Fin 4, if k = i then abs (a i - a k) / (b 3 - b 0) else 0) +
          (∑ k : Fin 4, if k = j then abs (a i - a k) / (b 3 - b 0) else 0) :=
            Finset.sum_add_distrib
      _ = _ := by simp
  have heij' : (∑ k : Fin 4, if k = i then abs (a i - a k) / (b 3 - b 0)
      else if k = j then abs (a i - a k) / (b 3 - b 0) else 0) = 1 := by
    rw [← heij]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [hki, hkj, div_eq_mul_inv]
  rw [hsum] at heij'
  simp only [sub_self, abs_zero, zero_div, zero_add] at heij'
  have habs : abs (a i - a j) = b 3 - b 0 := by
    field_simp [hR] at heij'
    exact heij'
  have hend : (i = p 0 ∧ j = p 3) ∨ (i = p 3 ∧ j = p 0) := by
    rcases le_total (a i) (a j) with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at habs
      have hai : a i = b 0 := by
        have := hmin i
        have := hmax j
        linarith
      have haj : a j = b 3 := by
        have := hmin i
        have := hmax j
        linarith
      left
      exact ⟨ha (by simpa [b] using hai), ha (by simpa [b] using haj)⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at habs
      have haj : a j = b 0 := by
        have := hmin j
        have := hmax i
        linarith
      have hai : a i = b 3 := by
        have := hmin j
        have := hmax i
        linarith
      right
      exact ⟨ha (by simpa [b] using hai), ha (by simpa [b] using haj)⟩
  have hymem : y ∈ solution_set ha := by
    apply Set.mem_singleton_iff.mpr
    funext k
    have hk0 : order a k = 0 ↔ k = p 0 := by
      constructor
      · intro h
        exact (bijective_order ha).1 (h.trans (hp 0).symm)
      · rintro rfl
        exact hp 0
    have hk3 : order a k = 3 ↔ k = p 3 := by
      constructor
      · intro h
        exact (bijective_order ha).1 (h.trans (hp 3).symm)
      · rintro rfl
        exact hp 3
    have hn0 : nth_smallest ha 0 = b 0 := rfl
    have hn3 : nth_smallest ha 3 = b 3 := rfl
    rcases hend with hend | hend
    · rw [hyfun, hend.1, hend.2]
      by_cases h0 : k = p 0 <;> by_cases h3 : k = p 3 <;>
        simp [h0, h3, hp, hk0, hk3, hn0, hn3]
    · rw [hyfun, hend.1, hend.2]
      by_cases h0 : k = p 0 <;> by_cases h3 : k = p 3 <;>
        simp [h0, h3, hp, hk0, hk3, hn0, hn3]
  have eq_unique (u v : Fin 4 → ℝ)
      (hu : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * u j = 1)
      (hv : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * v j = 1) : u = v := by
    let z : Fin 4 → ℝ := fun k ↦ u (p k) - v (p k)
    have hsorted (w : Fin 4 → ℝ)
        (hw : ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * w j = 1)
        (r : Fin 4) : ∑ k : Fin 4, abs (b r - b k) * w (p k) = 1 := by
      calc
        ∑ k : Fin 4, abs (b r - b k) * w (p k) =
            ∑ k : Fin 4, abs (a (p r) - a (p k)) * w (p k) := by rfl
        _ = ∑ k : Fin 4, abs (a (p r) - a k) * w k := by
          simpa [ep] using (Equiv.sum_comp ep (fun k ↦ abs (a (p r) - a k) * w k))
        _ = 1 := hw (p r)
    have hz (r : Fin 4) : ∑ k : Fin 4, abs (b r - b k) * z k = 0 := by
      have huu := hsorted u hu r
      have hvv := hsorted v hv r
      dsimp [z]
      calc
        ∑ k, |b r - b k| * (u (p k) - v (p k)) =
            (∑ k, |b r - b k| * u (p k)) - (∑ k, |b r - b k| * v (p k)) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = 0 := by rw [huu, hvv]; norm_num
    have e0 := hz 0
    have e1 := hz 1
    have e2 := hz 2
    have e3 := hz 3
    simp [Fin.sum_univ_four,
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hb01)),
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hb02)),
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hb03)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb01)),
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hb12)),
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hb13)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb02)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb12)),
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hb23)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb03)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb13)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_lt hb23))] at e0 e1 e2 e3
    let q₀ := b 1 - b 0
    let q₁ := b 2 - b 1
    let q₂ := b 3 - b 2
    have hq₀ : q₀ ≠ 0 := by dsimp [q₀]; linarith
    have hq₁ : q₁ ≠ 0 := by dsimp [q₁]; linarith
    have hq₂ : q₂ ≠ 0 := by dsimp [q₂]; linarith
    have hqs : q₀ + q₁ + q₂ ≠ 0 := by dsimp [q₀, q₁, q₂]; linarith
    have d0 : (-4*q₀*q₁*q₂*(q₀+q₁+q₂))*z 0 = 0 := by
      linear_combination 2*q₁*q₂*(q₁+q₂)*e0 - 2*q₁*q₂*(q₀+q₁+q₂)*e1 - 2*q₀*q₁*q₂*e3
    have d1 : (-4*q₀*q₁*q₂*(q₀+q₁+q₂))*z 1 = 0 := by
      linear_combination -2*q₁*q₂*(q₀+q₁+q₂)*e0 + 2*q₂*(q₀+q₁)*(q₀+q₁+q₂)*e1 - 2*q₀*q₂*(q₀+q₁+q₂)*e2
    have d2 : (-4*q₀*q₁*q₂*(q₀+q₁+q₂))*z 2 = 0 := by
      linear_combination -2*q₀*q₂*(q₀+q₁+q₂)*e1 + 2*q₀*(q₁+q₂)*(q₀+q₁+q₂)*e2 - 2*q₀*q₁*(q₀+q₁+q₂)*e3
    have d3 : (-4*q₀*q₁*q₂*(q₀+q₁+q₂))*z 3 = 0 := by
      linear_combination -2*q₀*q₁*q₂*e0 - 2*q₀*q₁*(q₀+q₁+q₂)*e2 + 2*q₀*q₁*(q₀+q₁)*e3
    have hd : -4*q₀*q₁*q₂*(q₀+q₁+q₂) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hq₀) hq₁) hq₂) hqs
    have dz0 := (mul_eq_zero.mp d0).resolve_left hd
    have dz1 := (mul_eq_zero.mp d1).resolve_left hd
    have dz2 := (mul_eq_zero.mp d2).resolve_left hd
    have dz3 := (mul_eq_zero.mp d3).resolve_left hd
    funext k
    obtain ⟨r, rfl⟩ := hp_bij.2 k
    have hr : z r = 0 := by
      have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hcases with h | h | h | h
      · simpa [h] using dz0
      · simpa [h] using dz1
      · simpa [h] using dz2
      · simpa [h] using dz3
    dsimp [z] at hr
    linarith
  constructor
  · intro hx
    have hxy := eq_unique x y hx hyeq
    rw [hxy]
    exact hymem
  · intro hx
    have hxy : x = y := by
      exact Set.mem_singleton_iff.mp hx |>.trans (Set.mem_singleton_iff.mp hymem).symm
    rw [hxy]
    exact hyeq
