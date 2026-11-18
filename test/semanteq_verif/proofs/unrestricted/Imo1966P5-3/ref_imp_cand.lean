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
theorem imo1966_p5_assumed
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := sorry

lemma fin4_mk_two (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := Fin.ext rfl
lemma fin4_mk_three (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := Fin.ext rfl

lemma two_point_equations (a : Fin 4 → ℝ) (ha : Function.Injective a) (u v : Fin 4) (huv : u ≠ v)
    (hmin : ∀ i, a u ≤ a i) (hmax : ∀ i, a i ≤ a v) :
    ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) *
      (if j = u ∨ j = v then 1 / (a v - a u) else 0) = 1 := by
  intro i
  have huv' : a v - a u ≠ 0 := by
    exact sub_ne_zero.mpr (ha.ne huv).symm
  have hs : (∑ j : Fin 4, abs (a i - a j) *
      (if j = u ∨ j = v then 1 / (a v - a u) else 0)) =
      abs (a i - a u) / (a v - a u) + abs (a i - a v) / (a v - a u) := by
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (i := u) (by simp)]
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ \ {u}) (i := v)]
    · have hz : (∑ x ∈ (Finset.univ \ {u}) \ {v}, abs (a i - a x) *
          (if x = u ∨ x = v then 1 / (a v - a u) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton] at hx
        simp [hx.1.2, hx.2]
      rw [hz]
      simp [huv, huv.symm, div_eq_mul_inv]
    · simp [huv.symm]
  rw [hs, abs_of_nonneg (sub_nonneg.mpr (hmin i)), abs_of_nonpos (sub_nonpos.mpr (hmax i))]
  field_simp
  ring

def tupleFun (p : ℝ × ℝ × ℝ × ℝ) : Fin 4 → ℝ := ![p.1, p.2.1, p.2.2.1, p.2.2.2]

lemma tupleFun_injective : Function.Injective tupleFun := by
  intro p q h
  rcases p with ⟨p1, p2, p3, p4⟩
  rcases q with ⟨q1, q2, q3, q4⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [tupleFun] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

lemma tuple_equations_iff (p : ℝ × ℝ × ℝ × ℝ) (a₁ a₂ a₃ a₄ : ℝ) :
    (let (x₁, x₂, x₃, x₄) := p;
      |a₁ - a₂| * x₂ + |a₁ - a₃| * x₃ + |a₁ - a₄| * x₄ = 1 ∧
      |a₂ - a₁| * x₁ + |a₂ - a₃| * x₃ + |a₂ - a₄| * x₄ = 1 ∧
      |a₃ - a₁| * x₁ + |a₃ - a₂| * x₂ + |a₃ - a₄| * x₄ = 1 ∧
      |a₄ - a₁| * x₁ + |a₄ - a₂| * x₂ + |a₄ - a₃| * x₃ = 1) ↔
    ∀ i : Fin 4, ∑ j : Fin 4,
      abs ((![a₁, a₂, a₃, a₄] : Fin 4 → ℝ) i - (![a₁, a₂, a₃, a₄] : Fin 4 → ℝ) j) * tupleFun p j = 1 := by
  rcases p with ⟨x1, x2, x3, x4⟩
  simp only
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> norm_num [Fin.sum_univ_four, tupleFun, fin4_mk_two, fin4_mk_three] at h0 h1 h2 h3 ⊢
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    norm_num [Fin.sum_univ_four, tupleFun, fin4_mk_two, fin4_mk_three] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩

lemma tuple_equations_unique (a₁ a₂ a₃ a₄ : ℝ)
    (ha : Function.Injective (![a₁, a₂, a₃, a₄] : Fin 4 → ℝ))
    (p q : ℝ × ℝ × ℝ × ℝ)
    (hp : (let (x₁, x₂, x₃, x₄) := p;
      |a₁ - a₂| * x₂ + |a₁ - a₃| * x₃ + |a₁ - a₄| * x₄ = 1 ∧
      |a₂ - a₁| * x₁ + |a₂ - a₃| * x₃ + |a₂ - a₄| * x₄ = 1 ∧
      |a₃ - a₁| * x₁ + |a₃ - a₂| * x₂ + |a₃ - a₄| * x₄ = 1 ∧
      |a₄ - a₁| * x₁ + |a₄ - a₂| * x₂ + |a₄ - a₃| * x₃ = 1))
    (hq : (let (x₁, x₂, x₃, x₄) := q;
      |a₁ - a₂| * x₂ + |a₁ - a₃| * x₃ + |a₁ - a₄| * x₄ = 1 ∧
      |a₂ - a₁| * x₁ + |a₂ - a₃| * x₃ + |a₂ - a₄| * x₄ = 1 ∧
      |a₃ - a₁| * x₁ + |a₃ - a₂| * x₂ + |a₃ - a₄| * x₄ = 1 ∧
      |a₄ - a₁| * x₁ + |a₄ - a₂| * x₂ + |a₄ - a₃| * x₃ = 1)) : p = q := by
  apply tupleFun_injective
  have hp' := (tuple_equations_iff p a₁ a₂ a₃ a₄).mp hp
  have hq' := (tuple_equations_iff q a₁ a₂ a₃ a₄).mp hq
  have hpS := (imo1966_p5_assumed (tupleFun p) ![a₁,a₂,a₃,a₄] ha).mp hp'
  have hqS := (imo1966_p5_assumed (tupleFun q) ![a₁,a₂,a₃,a₄] ha).mp hq'
  exact Set.mem_singleton_iff.mp hpS |>.trans (Set.mem_singleton_iff.mp hqS).symm


-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement 
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
       else False)) := by

  let A : Fin 4 → ℝ := ![a₁, a₂, a₃, a₄]
  have hA : Function.Injective A := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [A] at hij ⊢
    all_goals tauto
  let M := max_of_four a₁ a₂ a₃ a₄
  let m := min_of_four a₁ a₂ a₃ a₄
  have hmin : ∀ i, m ≤ A i := by
    intro i
    fin_cases i <;> simp [m, M, A, min_of_four]
  have hmax : ∀ i, A i ≤ M := by
    intro i
    fin_cases i <;> simp [m, M, A, max_of_four]
  have hmin_mem : ∃ u : Fin 4, A u = m := by
    rcases min_choice a₁ (min a₂ (min a₃ a₄)) with ho | ho
    · refine ⟨0, ?_⟩
      change a₁ = min a₁ (min a₂ (min a₃ a₄))
      exact ho.symm
    rcases min_choice a₂ (min a₃ a₄) with hi | hi
    · refine ⟨1, ?_⟩
      change a₂ = min a₁ (min a₂ (min a₃ a₄))
      exact hi.symm.trans ho.symm
    rcases min_choice a₃ a₄ with hi2 | hi2
    · refine ⟨2, ?_⟩
      change a₃ = min a₁ (min a₂ (min a₃ a₄))
      exact hi2.symm.trans hi.symm |>.trans ho.symm
    · refine ⟨3, ?_⟩
      change a₄ = min a₁ (min a₂ (min a₃ a₄))
      exact hi2.symm.trans hi.symm |>.trans ho.symm
  have hmax_mem : ∃ v : Fin 4, A v = M := by
    rcases max_choice a₁ (max a₂ (max a₃ a₄)) with ho | ho
    · refine ⟨0, ?_⟩
      change a₁ = max a₁ (max a₂ (max a₃ a₄))
      exact ho.symm
    rcases max_choice a₂ (max a₃ a₄) with hi | hi
    · refine ⟨1, ?_⟩
      change a₂ = max a₁ (max a₂ (max a₃ a₄))
      exact hi.symm.trans ho.symm
    rcases max_choice a₃ a₄ with hi2 | hi2
    · refine ⟨2, ?_⟩
      change a₃ = max a₁ (max a₂ (max a₃ a₄))
      exact hi2.symm.trans hi.symm |>.trans ho.symm
    · refine ⟨3, ?_⟩
      change a₄ = max a₁ (max a₂ (max a₃ a₄))
      exact hi2.symm.trans hi.symm |>.trans ho.symm
  obtain ⟨u, hu⟩ := hmin_mem
  obtain ⟨v, hv⟩ := hmax_mem
  have huv : u ≠ v := by
    intro huv
    have hMm : M = m := by rw [← hv, ← hu, huv]
    have h01 : A 0 = A 1 := le_antisymm
      (calc A 0 ≤ M := hmax 0
            _ = m := hMm
            _ ≤ A 1 := hmin 1)
      (calc A 1 ≤ M := hmax 1
            _ = m := hMm
            _ ≤ A 0 := hmin 0)
    exact (hA.ne (by decide)) h01
  let X : Fin 4 → ℝ := fun i => if i = u ∨ i = v then 1 / (M - m) else 0
  let p : ℝ × ℝ × ℝ × ℝ := (X 0, X 1, X 2, X 3)
  have hX : ∀ i : Fin 4, ∑ j : Fin 4, abs (A i - A j) * X j = 1 := by
    intro i
    simpa [X, hu, hv] using two_point_equations A hA u v huv
      (fun k => by rw [hu]; exact hmin k) (fun k => by rw [hv]; exact hmax k) i
  have hpEq : (let (x₁, x₂, x₃, x₄) := p
      |a₁ - a₂| * x₂ + |a₁ - a₃| * x₃ + |a₁ - a₄| * x₄ = 1 ∧
      |a₂ - a₁| * x₁ + |a₂ - a₃| * x₃ + |a₂ - a₄| * x₄ = 1 ∧
      |a₃ - a₁| * x₁ + |a₃ - a₂| * x₂ + |a₃ - a₄| * x₄ = 1 ∧
      |a₄ - a₁| * x₁ + |a₄ - a₂| * x₂ + |a₄ - a₃| * x₃ = 1) := by
    apply (tuple_equations_iff p a₁ a₂ a₃ a₄).mpr
    have htp : tupleFun p = X := by
      funext i
      fin_cases i <;> simp [tupleFun, p, fin4_mk_two, fin4_mk_three]
    simpa [A, htp] using hX
  refine ⟨p, ?_, ?_⟩
  · rcases hpEq with ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    have hMiff : ∀ i, A i = M ↔ i = v := fun i =>
      ⟨fun hi => hA (hi.trans hv.symm), fun hi => hi ▸ hv⟩
    have hmiff : ∀ i, A i = m ↔ i = u := fun i =>
      ⟨fun hi => hA (hi.trans hu.symm), fun hi => hi ▸ hu⟩
    have hM0 := hMiff 0; have hM1 := hMiff 1
    have hM2 := hMiff 2; have hM3 := hMiff 3
    have hm0 := hmiff 0; have hm1 := hmiff 1
    have hm2 := hmiff 2; have hm3 := hmiff 3
    simp [A] at hM0 hM1 hM2 hM3 hm0 hm1 hm2 hm3
    have hMdef : max_of_four a₁ a₂ a₃ a₄ = M := rfl
    have hmdef : min_of_four a₁ a₂ a₃ a₄ = m := rfl
    dsimp [p]
    fin_cases u <;> fin_cases v <;>
      simp [X, hMdef, hmdef, hM0, hM1, hM2, hM3, hm0, hm1, hm2, hm3] at huv ⊢
  · intro q hq
    symm
    apply tuple_equations_unique a₁ a₂ a₃ a₄ hA p q hpEq
    exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩

