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
  have hx0 : x 0 = 1 := by
    change (f 0 : ℝ) = 1
    exact_mod_cast hf₁
  have hx1 : x 1 = (f 1 : ℝ) := rfl
  have hx2 : x 2 = (f 1 : ℝ) := by
    change (f 2 : ℝ) = (f 1 : ℝ)
    exact_mod_cast hf₂.symm
  have hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2) := by
    intro n hn
    have hr := hf₃ (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    change (f (n + 1) : ℝ) = 2 * (f n : ℝ) * (f (n - 1) : ℝ) - (f (n - 2) : ℝ)
    exact_mod_cast hr
  have hxzero : ∃ n, x n = 0 := by
    obtain ⟨n, hn⟩ := hf
    refine ⟨n, ?_⟩
    change (f n : ℝ) = 0
    exact_mod_cast hn
  obtain ⟨c, hc, hper⟩ := exercise_2018_b4_assumed (f 1 : ℝ) x hx0 hx1 hx2 hxn hxzero
  refine ⟨c, c, hc, ?_⟩
  intro k
  have hp := (hper (k * c)).symm
  dsimp [x] at hp
  rw [Nat.add_comm c (k * c)]
  exact_mod_cast hp
