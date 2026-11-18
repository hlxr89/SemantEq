import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℕ → ℤ} (hf₁ : f 0 = 1) (hf₂ : f 1 = f 2) (hf₃ : ∀ n ≥ 2, f n = 2*f (n-1)*f (n-2) - f (n-3)) (hf : ∃ n, f n = 0) : ∃ m n : ℕ, m ≠ 0 ∧ ∀ k : ℕ, f (k*m) = f (n+k*m) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  -- not proved: the candidate conclusion is vacuous when its existential witness n is 0, so it cannot transport periodicity of x
  sorry
