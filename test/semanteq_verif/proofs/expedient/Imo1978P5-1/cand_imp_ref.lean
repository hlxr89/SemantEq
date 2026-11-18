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
  let M := (∑ k ∈ Finset.Icc 1 n, f k) + 1
  let a : ℕ → ℕ := fun k => if k = 0 then M else if k ≤ n then f k else M + k
  have hM : ∀ k ∈ Finset.Icc 1 n, f k < M := by
    intro k hk
    dsimp [M]
    have := Finset.single_le_sum (s := Finset.Icc 1 n) (fun i _ => Nat.zero_le (f i)) hk
    omega
  have ha_pos : ∀ k, 0 < a k := by
    intro k
    dsimp [a]
    split_ifs with hk hkn
    · dsimp [M]
      omega
    · exact h₀ k (Nat.pos_of_ne_zero hk)
    · dsimp [M]
      omega
  have ha_inj : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      by_cases hj0 : j = 0
      · exact (hij hj0.symm).elim
      · by_cases hjn : j ≤ n
        · have hjmem : j ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
            ⟨Nat.pos_of_ne_zero hj0, hjn⟩
          simp only [a, if_pos rfl, if_neg hj0, if_pos hjn]
          exact Nat.ne_of_gt (hM j hjmem)
        · simp only [a, if_pos rfl, if_neg hj0, if_neg hjn]
          omega
    · by_cases hj0 : j = 0
      · subst j
        by_cases hin : i ≤ n
        · have himem : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
            ⟨Nat.pos_of_ne_zero hi0, hin⟩
          simp only [a, if_neg hi0, if_pos hin, if_pos rfl]
          exact Nat.ne_of_lt (hM i himem)
        · simp only [a, if_neg hi0, if_neg hin, if_pos rfl]
          omega
      · by_cases hin : i ≤ n
        · by_cases hjn : j ≤ n
          · simpa only [a, if_neg hi0, if_pos hin, if_neg hj0, if_pos hjn] using
              h₁ i j (Nat.pos_of_ne_zero hi0) (Nat.pos_of_ne_zero hj0) hij
          · have himem : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
              ⟨Nat.pos_of_ne_zero hi0, hin⟩
            have hlt := hM i himem
            simp only [a, if_neg hi0, if_pos hin, if_neg hj0, if_neg hjn]
            omega
        · by_cases hjn : j ≤ n
          · have hjmem : j ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
              ⟨Nat.pos_of_ne_zero hj0, hjn⟩
            have hlt := hM j hjmem
            simp only [a, if_neg hi0, if_neg hin, if_neg hj0, if_pos hjn]
            omega
          · simp only [a, if_neg hi0, if_neg hin, if_neg hj0, if_neg hjn]
            omega
  have hq := problem_statement_assumed a ha_pos ha_inj n
  have hagree : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkn⟩
    simp only [a, if_neg (Nat.ne_of_gt hk1), if_pos hkn]
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2) =
        ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hagree k hk]
  rw [hsum] at hq
  have hq' :
      (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ)) ≤
        ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := hq
  have hl :
      ((↑(∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / k) : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
    push_cast
    norm_num
  have hf :
      ((↑(∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2) : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n, (f k : ℝ) / k^2 := by
    push_cast
    norm_num
  calc
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k =
        (↑(∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / k) : ℝ) := hl.symm
    _ ≤ (↑(∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2) : ℝ) := by
      exact_mod_cast hq'
    _ = ∑ k ∈ Finset.Icc 1 n, (f k : ℝ) / k^2 := hf
