import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a : ℕ → ℕ) 
  (h_pos : ∀ k, 0 < a k)
  (h_distinct : ∀ i j, i ≠ j → a i ≠ a j) :
  ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2 ≥ ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1978_p5
    (n : ℕ)
    (f : ℕ → ℕ)
    (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
    (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  let g : ℕ → ℕ := fun k => if k = 0 then n + 1 else if k ≤ n then k else k + 1
  have hg_pos : ∀ k, 0 < g k := by
    intro k
    by_cases hk0 : k = 0
    · simp only [g, if_pos hk0]
      exact Nat.zero_lt_succ n
    · by_cases hkn : k ≤ n
      · simp only [g, if_neg hk0, if_pos hkn]
        exact Nat.pos_of_ne_zero hk0
      · simp only [g, if_neg hk0, if_neg hkn]
        exact Nat.zero_lt_succ k
  have hg_inj : Function.Injective g := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      by_cases hj0 : j = 0
      · exact hj0.symm
      · by_cases hjn : j ≤ n
        · simp only [g, if_pos rfl, if_neg hj0, if_pos hjn] at hij
          exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_le hjn)) hij.symm)
        · simp only [g, if_pos rfl, if_neg hj0, if_neg hjn] at hij
          have hnj : n = j := Nat.add_right_cancel hij
          exact False.elim (hjn hnj.symm.le)
    · by_cases hj0 : j = 0
      · subst j
        by_cases hin : i ≤ n
        · simp only [g, if_neg hi0, if_pos hin, if_pos rfl] at hij
          exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_of_le hin)) hij)
        · simp only [g, if_neg hi0, if_neg hin, if_pos rfl] at hij
          have hin' : i = n := Nat.add_right_cancel hij
          exact False.elim (hin hin'.le)
      · by_cases hin : i ≤ n
        · by_cases hjn : j ≤ n
          · simpa only [g, if_neg hi0, if_neg hj0, if_pos hin, if_pos hjn] using hij
          · simp only [g, if_neg hi0, if_neg hj0, if_pos hin, if_neg hjn] at hij
            have hijlt : i < j + 1 :=
              Nat.lt_trans (Nat.lt_of_le_of_lt hin (Nat.lt_of_not_ge hjn))
                (Nat.lt_succ_self j)
            exact False.elim ((Nat.ne_of_lt hijlt) hij)
        · by_cases hjn : j ≤ n
          · simp only [g, if_neg hi0, if_neg hj0, if_neg hin, if_pos hjn] at hij
            have hjilt : j < i + 1 :=
              Nat.lt_trans (Nat.lt_of_le_of_lt hjn (Nat.lt_of_not_ge hin))
                (Nat.lt_succ_self i)
            exact False.elim ((Nat.ne_of_lt hjilt) hij.symm)
          · simp only [g, if_neg hi0, if_neg hj0, if_neg hin, if_neg hjn] at hij
            exact Nat.add_right_cancel hij
  let a : ℕ → ℕ := fun k => f (g k)
  have ha_pos : ∀ k, 0 < a k := fun k => h₀ (g k) (hg_pos k)
  have ha_inj : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    exact h₁ (g i) (g j) (hg_pos i) (hg_pos j) (fun h => hij (hg_inj h))
  have h := problem_statement_assumed a ha_pos ha_inj n
  have h_agree : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk'.1)
    simp only [a, g, if_neg hk0, if_pos hk'.2]
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2) =
        ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [h_agree k hk]
  rw [hsum] at h
  have hcast := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_one,
    Rat.cast_pow] using hcast
