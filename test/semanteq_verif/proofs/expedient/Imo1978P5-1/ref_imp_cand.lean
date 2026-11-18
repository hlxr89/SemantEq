import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem imo1978_p5_assumed
    (n : ℕ)
    (f : ℕ → ℕ)
    (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
    (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a : ℕ → ℕ) 
  (h_pos : ∀ k, 0 < a k)
  (h_distinct : ∀ i j, i ≠ j → a i ≠ a j) :
  ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2 ≥ ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) := by
  intro n
  by_cases hn : 0 < n
  · change (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ)) ≤
      ∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2
    have hr := imo1978_p5_assumed n a (fun m _ => h_pos m)
      (fun p q _ _ hpq => h_distinct p q hpq) hn
    have hl :
        ((↑(∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / k) : ℝ)) =
          ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
      push_cast
      norm_num
    have ha :
        ((↑(∑ k ∈ Finset.Icc 1 n, (a k : ℚ) / (k : ℚ)^2) : ℝ)) =
          ∑ k ∈ Finset.Icc 1 n, (a k : ℝ) / k^2 := by
      push_cast
      norm_num
    rw [← hl, ← ha] at hr
    exact_mod_cast hr
  · simp [Nat.eq_zero_of_not_pos hn]
