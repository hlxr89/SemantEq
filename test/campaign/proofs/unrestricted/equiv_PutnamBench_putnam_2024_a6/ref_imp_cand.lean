import Mathlib

open scoped Real
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
noncomputable abbrev putnam_2024_a6_solution : ℕ → ℝ := fun n => 10^(n*(n-1)/2 : ℕ)

-- ===== assumed statement (antecedent) =====
theorem putnam_2024_a6_assumed
    (c : ℕ → ℝ)
    (n : ℕ)
    (h₀ : ∀ᶠ x in 𝓝 0,
      HasSum (fun k => c k * x ^ k) ((1 - 3 * x - √(1 - 14 * x + 9 * x ^ 2)) / 4))
    (h₁ : 0 < n) :
    (Matrix.of fun (i j : Fin n) => c (i + j + 1)).det = putnam_2024_a6_solution n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2024_a6_alt
    (c : ℕ → ℝ)
    (n : ℕ)
    (h₀ : ∀ᶠ x in 𝓝 0,
      HasSum (fun k => c k * x ^ k) ((1 - 3 * x - √(1 - 14 * x + 9 * x ^ 2)) / 4))
    (h₁ : 0 < n) :
    (Matrix.of fun (i j : Fin n) => c (i + j + 1)).det = 10^(n*(n-1)/2 : ℕ) := by
  exact putnam_2024_a6_assumed c n h₀ h₁
