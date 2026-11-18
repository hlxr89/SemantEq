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
  let a : ℕ → ℕ := fun k => if k = 0 then f (n + 1) else if k ≤ n then f k else f (k + 1)
  have ha : ∀ k, a k > 0 := by
    intro k
    simp only [a]
    split_ifs with hk hkn
    · exact h₀ (n + 1) (by omega)
    · exact h₀ k (by omega)
    · exact h₀ (k + 1) (by omega)
  have hainj : ∀ i j, i ≠ j → a i ≠ a j := by
    intro i j hij
    simp only [a]
    split_ifs with hi hin hj hjn
    · omega
    · exact h₁ (n + 1) j (by omega) (by omega) (by omega)
    · exact h₁ (n + 1) (j + 1) (by omega) (by omega) (by omega)
    · exact h₁ i (n + 1) (by omega) (by omega) (by omega)
    · exact h₁ i j (by omega) (by omega) hij
    · exact h₁ i (j + 1) (by omega) (by omega) (by omega)
    · exact h₁ (i + 1) (n + 1) (by omega) (by omega) (by omega)
    · exact h₁ (i + 1) j (by omega) (by omega) (by omega)
    · exact h₁ (i + 1) (j + 1) (by omega) (by omega) (by omega)
  have h := problem_statement_assumed a ha hainj n (by omega)
  have hae : ∀ k ∈ Finset.Icc 1 n, a k = f k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [a]
    rw [if_neg (by omega), if_pos (by omega)]
  have hs : (∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2) =
      ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hae k hk]
  rw [hs] at h
  change (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ)) ≤
    ∑ k ∈ Finset.Icc 1 n, (f k : ℚ) / (k : ℚ)^2 at h
  rw [← Rat.cast_le (K := ℝ)] at h
  push_cast at h
  exact h
