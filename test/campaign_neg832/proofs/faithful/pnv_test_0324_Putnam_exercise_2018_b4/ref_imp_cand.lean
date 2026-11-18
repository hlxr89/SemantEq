import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2018_b4_assumed (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℕ → ℤ} (hf₁ : f 0 = 1) (hf₂ : f 1 = f 2) (hf₃ : ∀ n ≥ 2, f n = 2*f (n-1)*f (n-2) - f (n-3)) (hf : ∃ n, f n = 0) : ∃ m n : ℕ, m ≠ 0 ∧ ∀ k : ℕ, f (k*m) = f (n+k*m) := by
  let x : ℕ → ℝ := fun n => f n
  obtain ⟨c, hc0, hc⟩ := exercise_2018_b4_assumed (f 1 : ℝ) x
    (by simp [x, hf₁]) (by simp [x]) (by simp [x, hf₂])
    (by
      intro n hn
      dsimp [x]
      rw [hf₃ (n + 1) (by omega)]
      push_cast
      congr 2)
    (by
      obtain ⟨n, hn⟩ := hf
      exact ⟨n, by simp [x, hn]⟩)
  refine ⟨c, c, hc0, ?_⟩
  intro k
  have hk : x (k * c) = x (c + k * c) := by
    simpa [Nat.add_comm] using (hc (k * c)).symm
  change (f (k * c) : ℝ) = (f (c + k * c) : ℝ) at hk
  exact_mod_cast hk
