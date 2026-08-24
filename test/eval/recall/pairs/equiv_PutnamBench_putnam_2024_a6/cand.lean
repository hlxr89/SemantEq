/-
Benchmark: PutnamBench (trishullab/PutnamBench, lean4)
Problem: putnam_2024_a6
-/
import Mathlib

open scoped Real
open scoped Topology

noncomputable abbrev putnam_2024_a6_solution : ℕ → ℝ := fun n => 10^(n*(n-1)/2 : ℕ)

/- ALT (G): the solution abbrev `putnam_2024_a6_solution n` is inlined as its literal value `10^(n*(n-1)/2 : ℕ)` -/
theorem putnam_2024_a6_alt
    (c : ℕ → ℝ)
    (n : ℕ)
    (h₀ : ∀ᶠ x in 𝓝 0,
      HasSum (fun k => c k * x ^ k) ((1 - 3 * x - √(1 - 14 * x + 9 * x ^ 2)) / 4))
    (h₁ : 0 < n) :
    (Matrix.of fun (i j : Fin n) => c (i + j + 1)).det = 10^(n*(n-1)/2 : ℕ) :=
  sorry
