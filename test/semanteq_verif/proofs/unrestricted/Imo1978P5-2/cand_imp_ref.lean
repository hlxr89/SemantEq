import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (a : ℕ → ℕ),
    (∀ k, a k > 0) →
    (∀ i j, i ≠ j → a i ≠ a j) →
    ∀ n : ℕ, n ≥ 1 →
      ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2 ≥ ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1978_p5
    (n : ℕ)
    (f : ℕ → ℕ)
    (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
    (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  let B : ℕ := (∑ k ∈ Finset.Icc 1 n, f k) + 1
  let a : ℕ → ℕ := fun k => if k ∈ Finset.Icc 1 n then f k else B + k
  have hf_le_sum {k : ℕ} (hk : k ∈ Finset.Icc 1 n) : f k ≤ ∑ j ∈ Finset.Icc 1 n, f j := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk
  have ha_pos : ∀ k, a k > 0 := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 n
    · have hk' := (Finset.mem_Icc.mp hk).1
      change (if k ∈ Finset.Icc 1 n then f k else B + k) > 0
      rw [if_pos hk]
      exact h₀ k hk'
    · change (if k ∈ Finset.Icc 1 n then f k else B + k) > 0
      rw [if_neg hk]
      exact Nat.add_pos_left (Nat.succ_pos _) k
  have ha_inj : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    simp only [a]
    by_cases hi : i ∈ Finset.Icc 1 n
    · by_cases hj : j ∈ Finset.Icc 1 n
      · simp only [hi, hj, if_true]
        exact h₁ i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
      · simp only [hi, hj, if_true, if_false]
        intro heq
        have hlt : f i < B := lt_of_le_of_lt (hf_le_sum hi) (Nat.lt_succ_self _)
        have hle : B ≤ B + j := Nat.le_add_right B j
        omega
    · by_cases hj : j ∈ Finset.Icc 1 n
      · simp only [hi, hj, if_true, if_false]
        intro heq
        have hlt : f j < B := lt_of_le_of_lt (hf_le_sum hj) (Nat.lt_succ_self _)
        have hle : B ≤ B + i := Nat.le_add_right B i
        omega
      · simp only [hi, hj, if_false]
        omega
  have hq := problem_statement_assumed a ha_pos ha_inj n h₂
  have ha_eq : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    change (if k ∈ Finset.Icc 1 n then f k else B + k) = f k
    rw [if_pos hk]
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ) ^ 2) =
        ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [ha_eq k hk]
  rw [hsum] at hq
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  simpa [Nat.cast_pow] using hr
