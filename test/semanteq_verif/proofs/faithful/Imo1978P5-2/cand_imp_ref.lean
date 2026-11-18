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
  let s : Finset ℕ := Finset.Icc 1 n
  let M : ℕ := ∑ k ∈ s, f k + 1
  let a : ℕ → ℕ := fun k => if k ∈ s then f k else M + k
  have hbound : ∀ k ∈ s, f k < M := by
    intro k hk
    have hle : f k ≤ ∑ j ∈ s, f j := by
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) hk
    dsimp [M]
    omega
  have ha_pos : ∀ k, a k > 0 := by
    intro k
    by_cases hk : k ∈ s
    · simp only [a, if_pos hk]
      exact h₀ k (by
        have := (Finset.mem_Icc.mp hk).1
        omega)
    · simp only [a, if_neg hk]
      dsimp [M]
      omega
  have ha_inj : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · simp only [a, if_pos hi, if_pos hj]
      exact h₁ i j
        (by have := (Finset.mem_Icc.mp hi).1; omega)
        (by have := (Finset.mem_Icc.mp hj).1; omega)
        hij
    · simp only [a, if_pos hi, if_neg hj]
      have hiM := hbound i hi
      omega
    · simp only [a, if_neg hi, if_pos hj]
      have hjM := hbound j hj
      omega
    · simp only [a, if_neg hi, if_neg hj]
      omega
  have hrat := problem_statement_assumed a ha_pos ha_inj n (by omega)
  have hagree : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    have hks : k ∈ s := by simpa only [s] using hk
    simp only [a, if_pos hks]
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2) =
        ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hagree k hk]
  rw [hsum] at hrat
  change (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k) ≤
    ∑ k ∈ Finset.Icc 1 n, ((f k) : ℝ) / k ^ 2
  have hcast :
      ((∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) : ℚ) : ℝ) ≤
        ((∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 : ℚ) : ℝ) := by
    exact_mod_cast hrat
  simpa using hcast
