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
  let s : Finset ℕ := Finset.Icc 1 n
  let B : ℕ := ∑ k ∈ s, f k
  let a : ℕ → ℕ := fun k => if k ∈ s then f k else B + k + 1
  have hf_le (k : ℕ) (hk : k ∈ s) : f k ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk
  have ha_pos : ∀ k, 0 < a k := by
    intro k
    simp only [a]
    split_ifs with hk
    · exact h₀ k (by simpa [s] using (Finset.mem_Icc.1 hk).1)
    · omega
  have ha_distinct : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    simp only [a]
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · simp only [hi, hj, ↓reduceIte]
      apply h₁ i j
      · simpa [s] using (Finset.mem_Icc.1 hi).1
      · simpa [s] using (Finset.mem_Icc.1 hj).1
      · exact hij
    · simp only [hi, hj, ↓reduceIte]
      have hle := hf_le i hi
      omega
    · simp only [hi, hj, ↓reduceIte]
      have hle := hf_le j hj
      omega
    · simp only [hi, hj, ↓reduceIte]
      omega
  have hq := problem_statement_assumed a ha_pos ha_distinct n
  have hsame : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    change (if k ∈ s then f k else B + k + 1) = f k
    rw [if_pos]
    simpa [s] using hk
  rw [Finset.sum_congr rfl (fun k hk => by rw [hsame k hk])] at hq
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  exact hr
