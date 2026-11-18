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
theorem problem_statement (a : ℕ → ℕ) (h_pos : ∀ k, k ≥ 1 → a k > 0) (h_distinct : ∀ k m, k ≥ 1 → m ≥ 1 → k ≠ m → a k ≠ a m) :
  ∀ n : ℕ, n ≥ 1 → (Finset.sum (Finset.Icc 1 n) (fun k => (a k : ℚ) / (k : ℚ)^2) : ℚ) ≥ (Finset.sum (Finset.Icc 1 n) (fun k => (1 : ℚ) / (k : ℚ))) := by
  intro n hn
  have h := imo1978_p5_assumed n a h_pos h_distinct hn
  rw [ge_iff_le]
  apply (Rat.cast_le (K := ℝ)).mp
  convert h using 1 <;> norm_cast <;> simp
