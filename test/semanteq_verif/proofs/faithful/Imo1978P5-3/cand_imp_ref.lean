import Mathlib
open Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a : ℕ → ℕ) (h_pos : ∀ k, k ≥ 1 → a k > 0) (h_distinct : ∀ k m, k ≥ 1 → m ≥ 1 → k ≠ m → a k ≠ a m) :
  ∀ n : ℕ, n ≥ 1 → (Finset.sum (Finset.Icc 1 n) (fun k => (a k : ℚ) / (k : ℚ)^2) : ℚ) ≥ (Finset.sum (Finset.Icc 1 n) (fun k => (1 : ℚ) / (k : ℚ))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1978_p5
    (n : ℕ)
    (f : ℕ → ℕ)
    (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
    (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  have h := problem_statement_assumed f h₀ h₁ n h₂
  have hc := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one] using hc
