/-
Autoformalized from NL only (blind); benchmark: Compfiles; problem: Usa1996P1.
-/
import Mathlib

/-- Prove that the average of the numbers n⬝sin(n π / 180)
for n ∈ {2,4,6,…,180} is 1/tan(π/180).

The set {2,4,…,180} has 90 elements, written as 2k for k ∈ {1,…,90}. -/
theorem Usa1996P1 :
    (∑ k ∈ Finset.Icc (1 : ℕ) 90,
        (2 * (k : ℝ)) * Real.sin (2 * (k : ℝ) * Real.pi / 180)) / 90 =
      1 / Real.tan (Real.pi / 180) :=
  sorry
